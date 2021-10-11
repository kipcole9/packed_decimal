defmodule BitstringDecimal do
  @moduledoc """
  Decimal arithmetic on *fixed* precision floating-point numbers.

  A number is represented by a signed coefficient and exponent such that: `sign
  * coefficient * 10 ^ exponent`. All numbers are represented and calculated
  exactly, but the result of an operation may be rounded depending on the
  context the operation is performed. Trailing
  zeros in the coefficient are never truncated to preserve the number of
  significant digits unless explicitly done so.

  There are also special values such as NaN (not a number) and ±Infinity.
  -0 and +0 are two distinct values.

  Some operation results are not defined and will return NaN.
  This kind of NaN is quiet, any operation returning a number will return
  NaN when given a quiet NaN (the NaN value will flow through all operations).

  Exceptional conditions are grouped into signals, each signal has a flag and a
  trap enabler in the context. Whenever a signal is triggered it's flag is set
  in the context and will be set until explicitly cleared. If the signal is trap
  enabled `Decimal.Error` will be raised.

  ## Specifications

    * [IBM's General Decimal Arithmetic Specification](http://speleotrove.com/decimal/decarith.html)
    * [IEEE standard 854-1987](http://web.archive.org/web/20150908012941/http://754r.ucbtest.org/standards/854.pdf)

  This library follows the above specifications for reference of arithmetic
  operation implementations, but the public APIs may differ to provide a
  more idiomatic Elixir interface.

  The specification models the sign of the number as 1, for a negative number,
  and 0 for a positive number. Internally this implementation models the sign as
  1 or -1 such that the complete number will be `sign * coefficient *
  10 ^ exponent` and will refer to the sign in documentation as either *positive*
  or *negative*.

  Since this implementation *does* have a maximum exponent, this section needs
  rewriting:
    There is currently no maximum or minimum values for the exponent. Because of
    that all numbers are "normal". This means that when an operation should,
    according to the specification, return a number that "underflows" 0 is returned
    instead of Etiny. This may happen when dividing a number with infinity.
    Additionally, overflow, underflow and clamped may never be signalled.
  """

  import Bitwise
  import Kernel, except: [abs: 1, div: 2, max: 2, min: 2, rem: 2, round: 1]
  alias PackedDecimal.Context
  alias PackedDecimal.Error

  @power_of_2_to_52 4_503_599_627_370_496

  @typedoc """
  The coefficient of the power of `10`. Non-negative because the sign is stored separately in `sign`.

    * `non_neg_integer` - when the `t` represents a number, instead of one of the special values below.
    * `:NaN` - Not a Number.
    * `:inf` - Infinity.

  """
  @type coefficient :: non_neg_integer | :NaN | :inf

  @typedoc """
  The exponent to which `10` is raised.
  """
  @type exponent :: integer

  @typedoc """

    * `1` for positive
    * `-1` for negative

  """
  @type sign :: 1 | -1

  @type signal ::
          :invalid_operation
          | :division_by_zero
          | :rounded
          | :inexact

  @typedoc """
  Rounding algorithm.

  See `Decimal.Context` for more information.
  """
  @type rounding ::
          :down
          | :half_up
          | :half_even
          | :ceiling
          | :floor
          | :half_down
          | :up

  defstruct [binary_decimal: 0]

  @typedoc """
    * `coef` - the coefficient of the power of `10`.
    * `exp` - the exponent of the power of `10`.
    * `sign` - `1` for positive, `0` for negative.

  """
  @type t ::  %__MODULE__{binary_decimal: bitstring()}

  @type decimal :: t | integer | String.t()

  # Bits for sign, nan and inf
  @flag_bits 3

  exp_bits = Application.compile_env(:binary_decimal, :exponent_bits, 10)
  max_bits = Application.compile_env(:binary_decimal, :max_bits, 60)
  coef_bits = max_bits - exp_bits - @flag_bits

  defp binary_decimal(exp_bits, coef_bits) do
    quote do
      %__MODULE__{binary_decimal:
        <<
          var!(sign)::integer-1,
          var!(nan)::integer-1,
          var!(inf)::integer-1,
          var!(exp)::signed-integer-unquote(exp_bits),
          var!(coef)::integer-unquote(coef_bits)
        >>
      }
    end
  end

  defmacrop binary_decimal do
    exp_bits = unquote(exp_bits)
    coef_bits = unquote(coef_bits)
    binary_decimal(exp_bits, coef_bits)
  end

  defmacro binary_decimal(n) do
    ast = binary_decimal(unquote(exp_bits), unquote(coef_bits))

    Macro.prewalk(ast, fn
      {:var!, meta, [{varname, [], module}]} ->
        varname = String.to_atom("#{varname}#{n}")
        {:var!, meta, [{varname, [], module}]}
      other ->
        other
    end)
  end

  defmacrop pack(sign, nan, inf, exp, coef) do
    exp_bits = unquote(exp_bits)
    coef_bits = unquote(coef_bits)

    quote do
      <<
        unquote(sign)::integer-1,
        unquote(nan)::integer-1,
        unquote(inf)::integer-1,
        unquote(exp)::signed-integer-unquote(exp_bits),
        unquote(coef)::integer-unquote(coef_bits)
      >>
    end
  end

  defmacrop nan(sign \\ 1) do
    exp_bits = unquote(exp_bits)
    coef_bits = unquote(coef_bits)

    quote do
      <<
        unquote(sign)::integer-1,
        1::integer-1,
        0::integer-1,
        0::signed-integer-unquote(exp_bits),
        0::integer-unquote(coef_bits)
      >>
    end
  end

  defmacrop infinity(sign \\ 1) do
    exp_bits = unquote(exp_bits)
    coef_bits = unquote(coef_bits)

    quote do
      <<
        unquote(sign)::integer-1,
        0::integer-1,
        1::integer-1,
        0::signed-integer-unquote(exp_bits),
        0::integer-unquote(coef_bits)
      >>
    end
  end

  # Integer precision n is between -2^b ≤ n ≤ 2^b – 1.

  # TODO
  # Note that the integer can be larger if we consider the
  # exponent as well but we will need to check the precision
  # to ensure we aren't dropping digits.

  @min_int -1 * trunc(:math.pow(2, coef_bits) - 1)
  @max_int trunc(:math.pow(2, coef_bits) - 1)

  # The compiler will optimize these steps out
  # but they are required to silence the unused
  # variable warnings coming from the function
  # head match

  defmacrop silence_unused do
    quote do
    _ = var!(sign); _ = var!(nan); _ = var!(inf); _ = var!(exp); _ = var!(coef)
    end
  end

  defmacrop silence_unused(n) do
    module = __MODULE__
    context = [context: module, import: Kernel]
    vars = ["sign", "nan", "inf", "exp", "coef"]

    quoted =
      Enum.map(vars, fn var ->
        {:=, [],
         [
           {:_, [], module},
           {:var!, context, [{String.to_atom("#{var}#{n}"), [], module}]}
        ]}
      end)

    {:__block__, [], quoted}
  end

  defmacrop error(flags, reason, result, context \\ nil) do
    quote bind_quoted: binding() do
      case handle_error(flags, reason, result, context) do
        {:ok, result} -> result
        {:error, error} -> raise Error, error
      end
    end
  end

  @doc """
  Returns `true` if number is NaN, otherwise `false`.
  """
  @spec nan?(t) :: boolean
  def nan?(binary_decimal()) when nan == 1, do: (silence_unused(); true)
  def nan?(binary_decimal()), do: (silence_unused(); false)

  @doc """
  Returns `true` if number is ±Infinity, otherwise `false`.
  """
  @spec inf?(t) :: boolean
  def inf?(binary_decimal()) when inf == 1, do: (silence_unused(); true)
  def inf?(binary_decimal()), do: (silence_unused(); false)

  @doc """
  Returns the sign of a packed decimal as either 1 or -1

  """
  @spec sign(t) :: sign()
  def sign(binary_decimal()) when sign == 1, do: (silence_unused(); 1)
  def sign(binary_decimal()) when sign == 0, do: (silence_unused(); -1)

  @doc """
  Returns `true` if argument is a decimal number, otherwise `false`.

  ## Examples

      iex> Decimal.is_decimal(Decimal.new(42))
      true

      iex> Decimal.is_decimal(42)
      false

  Allowed in guard tests.
  """

  defguard is_decimal(term)
    when elem(term, 0) == :binary_decimal and is_bitstring(elem(term,1))

  @doc """
  The absolute value of given number. Sets the number's sign to positive.
  """
  @spec abs(t) :: t
  def abs(binary_decimal() = binary_decimal) when sign == 1 do
    silence_unused()
    binary_decimal
  end

  def abs(binary_decimal()) do
    silence_unused()
    new(_sign = 1, nan, inf, exp, coef)
  end

  @doc """
  Adds two numbers together.

  ## Exceptional conditions

    * If one number is -Infinity and the other +Infinity, `:invalid_operation` will
      be signalled.

  ## Examples

      iex> Decimal.add(1, "1.1")
      #Decimal<2.1>

      iex> Decimal.add(1, "Inf")
      #Decimal<Infinity>

  """
  @spec add(decimal, decimal) :: t
  def add(binary_decimal() = decimal_1, decimal_2)
      when nan == 1 and is_decimal(decimal_2) do
    silence_unused()
    decimal_1
  end

  def add(decimal_1, binary_decimal() = decimal_2)
      when nan == 1 and is_decimal(decimal_1) do
    silence_unused()
    decimal_2
  end

  def add(binary_decimal(1) = num1, binary_decimal(2) = num2)
      when inf1 == 1 and inf2 == 1 and sign1 == sign2 do
    silence_unused(1); silence_unused(2)

    if exp1 > exp2 do
      num1
    else
      num2
    end
  end

  def add(binary_decimal(1), binary_decimal(2)) when inf1 == 1 and inf2 == 1 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "adding +Infinity and -Infinity", nan())
  end

  def add(binary_decimal(1) = num1, binary_decimal(2)) when inf1 == 1 do
    silence_unused(1); silence_unused(2)
    num1
  end

  def add(binary_decimal(1) = num1, binary_decimal(2)) when inf2 == 1 do
    silence_unused(1); silence_unused(2)
    num1
  end

  def add(binary_decimal(1), binary_decimal(2)) do
    silence_unused(1); silence_unused(2)
    sign1 = if sign1 <= 0, do: -1, else: 1
    sign2 = if sign2 <= 0, do: -1, else: 1

    {coef1, coef2} = add_align(coef1, exp1, coef2, exp2)
    coef = sign1 * coef1 + sign2 * coef2
    exp = Kernel.min(exp1, exp2)
    sign = add_sign(sign1, sign2, coef)
    context(new(sign, _nan = 0, _inf = 0, exp, Kernel.abs(coef)))
  end

  def add(num1, num2), do: add(decimal(num1), decimal(num2))

  @doc """
  Subtracts second number from the first. Equivalent to `Decimal.add/2` when the
  second number's sign is negated.

  ## Exceptional conditions

    * If one number is -Infinity and the other +Infinity `:invalid_operation` will
      be signalled.

  ## Examples

      iex> PackedDecimal.sub(1, "0.1")
      #Decimal<0.9>

      iex> PackedDecimal.sub(1, "Inf")
      #Decimal<-Infinity>

  """
  @spec sub(decimal, decimal) :: t
  def sub(binary_decimal(1) = num1, binary_decimal(2) = num2) do
    silence_unused(1); silence_unused(2)
    add(num1, put_sign(num2, -1))
  end

  def sub(num1, num2) do
    sub(decimal(num1), decimal(num2))
  end

  @doc """
  Compares two numbers numerically. If the first number is greater than the second
  `:gt` is returned, if less than `:lt` is returned, if both numbers are equal
  `:eq` is returned.

  Neither number can be a NaN.

  ## Examples

      iex> PackedDecimal.compare("1.0", 1)
      :eq

      iex> PackedDecimal.compare("Inf", -1)
      :gt

  """
  @spec compare(decimal, decimal) :: :lt | :gt | :eq
  def compare(binary_decimal(1), binary_decimal(2))
      when inf1 == 1 and inf2 == 1 and sign1 == sign2,
    do: (silence_unused(1); silence_unused(2); :eq)

  def compare(binary_decimal(1), binary_decimal(2))
      when inf1 == 1 and inf2 == 1 and sign1 < sign2,
    do: (silence_unused(1); silence_unused(2); :lt)

  def compare(binary_decimal(1), binary_decimal(2))
      when inf1 == 1 and inf2 == 1 and sign1 > sign2,
    do: (silence_unused(1); silence_unused(2); :gt)

  def compare(binary_decimal(1), _num2) when inf1 == 1 and sign1 == 1,
    do: (silence_unused(1); :gt)
  def compare(binary_decimal(1), _num2) when inf1 == 1 and sign1 == 0,
    do: (silence_unused(1); :lt)

  def compare(_num1, binary_decimal(2)) when inf2 == 1 and sign2 == 1,
    do: (silence_unused(2); :lt)
  def compare(_num1, binary_decimal(2)) when inf2 == 1 and sign2 == 0,
    do: (silence_unused(2); :gt)

  def compare(binary_decimal(1) = num1, _num2) when nan1 == 1,
    do: (silence_unused(1); error(:invalid_operation, "operation on NaN", num1))

  def compare(_num1, binary_decimal(2) = num2) when nan2 == 1,
    do: (silence_unused(2); error(:invalid_operation, "operation on NaN", num2))

  def compare(binary_decimal(1) = num1, binary_decimal(2) = num2) do
    silence_unused(1); silence_unused(2)

    case sub(num1, num2) do
      binary_decimal() when coef == 0 -> silence_unused(); :eq
      binary_decimal() when sign == 1 -> silence_unused(); :gt
      binary_decimal() when sign == 0 -> silence_unused(); :gt
    end
  end

  def compare(num1, num2) do
    compare(decimal(num1), decimal(num2))
  end

  @deprecated "Use compare/2 instead"
  @spec cmp(decimal, decimal) :: :lt | :eq | :gt
  def cmp(num1, num2) do
    compare(num1, num2)
  end

  @doc """
  Compares two numbers numerically and returns `true` if they are equal,
  otherwise `false`. If one of the operands is a quiet NaN this operation
  will always return `false`.

  ## Examples

      iex> PackedDecimal.equal?("1.0", 1)
      true

      iex> PackedDecimal.equal?(1, -1)
      false

  """
  @spec equal?(decimal, decimal) :: boolean
  def equal?(num1, num2) do
    eq?(num1, num2)
  end

  @doc """
  Compares two numbers numerically and returns `true` if they are equal,
  otherwise `false`. If one of the operands is a quiet NaN this operation
  will always return `false`.

  ## Examples

      iex> PackedDecimal.eq?("1.0", 1)
      true

      iex> PackedDecimal.eq?(1, -1)
      false

  """

  @spec eq?(decimal, decimal) :: boolean
  def eq?(binary_decimal(), _num2) when nan == 1, do: (silence_unused(); false)
  def eq?(_num1, binary_decimal()) when nan == 1, do: (silence_unused(); false)
  def eq?(num1, num2), do: compare(num1, num2) == :eq

  @doc """
  Compares two numbers numerically and returns `true` if the the first argument
  is greater than the second, otherwise `false`. If one the operands is a
  quiet NaN this operation will always return `false`.

  ## Examples

      iex> PackedDecimal.gt?("1.3", "1.2")
      true

      iex> PackedDecimal.gt?("1.2", "1.3")
      false

  """

  @spec gt?(decimal, decimal) :: boolean
  def gt?(binary_decimal(), _num2) when nan == 1, do: (silence_unused(); false)
  def gt?(_num1, binary_decimal()) when nan == 1, do: (silence_unused(); false)
  def gt?(num1, num2), do: compare(num1, num2) == :gt

  @doc """
  Compares two numbers numerically and returns `true` if the the first number is
  less than the second number, otherwise `false`. If one of the operands is a
  quiet NaN this operation will always return `false`.

  ## Examples

      iex> PackedDecimal.lt?("1.1", "1.2")
      true

      iex> PackedDecimal.lt?("1.4", "1.2")
      false

  """

  @spec lt?(decimal, decimal) :: boolean
  def lt?(binary_decimal(), _num2) when nan == 1, do: (silence_unused(); false)
  def lt?(_num1, binary_decimal()) when nan == 1, do: (silence_unused(); false)
  def lt?(num1, num2), do: compare(num1, num2) == :lt

  @doc """
  Divides two numbers.

  ## Exceptional conditions

    * If both numbers are ±Infinity `:invalid_operation` is signalled.
    * If both numbers are ±0 `:invalid_operation` is signalled.
    * If second number (denominator) is ±0 `:division_by_zero` is signalled.

  ## Examples

      iex> PackedDecimal.div(3, 4)
      #Decimal<0.75>

      iex> PackedDecimal.div("Inf", -1)
      #Decimal<-Infinity>

  """
  @spec div(decimal, decimal) :: t
  def div(binary_decimal(1) = num1, binary_decimal(2)) when nan1 == 1 do
    silence_unused(1); silence_unused(2)
    num1
  end

  def div(binary_decimal(1), binary_decimal(2) = num2) when nan2 == 1 do
    silence_unused(1); silence_unused(2)
    num2
  end

  def div(binary_decimal(1), binary_decimal(2)) when inf1 == 1 and inf2 == 1 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "±Infinity / ±Infinity", nan())
  end

  def div(binary_decimal(1) = num1, binary_decimal(2)) when inf1 == 1 do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: 0
    put_sign(num1, sign)
  end

  def div(binary_decimal(1), binary_decimal(2)) when inf2 == 1 do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: 0
    # TODO: Subnormal
    # exponent?
    new(sign, _nan = 0, _inf = 0, exp1 - exp2, _coef = 0)
  end

  def div(binary_decimal(1), binary_decimal(2)) when coef1 == 0 and coef2 == 0 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "0 / 0", nan())
  end

  def div(binary_decimal(1), binary_decimal(2)) when coef2 == 0 do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: 0
    error(:division_by_zero, nil, infinity(sign))
  end

  def div(binary_decimal(1), binary_decimal(2)) do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: 0

    if coef1 == 0 do
      context(new(sign, _nan = 0, _inf = 0, exp1 - exp2, _coef = 0), [])
    else
      prec10 = pow10(Context.get().precision)
      {coef1, coef2, adjust} = div_adjust(coef1, coef2, 0)
      {coef, adjust, _rem, signals} = div_calc(coef1, coef2, 0, adjust, prec10)

      context(new(sign, _nan = 0, _inf = 0, exp1 - exp2 - adjust, coef), signals)
    end
  end

  def div(num1, num2) do
    div(decimal(num1), decimal(num2))
  end

  @doc """
  Divides two numbers and returns the integer part.

  ## Exceptional conditions

    * If both numbers are ±Infinity `:invalid_operation` is signalled.
    * If both numbers are ±0 `:invalid_operation` is signalled.
    * If second number (denominator) is ±0 `:division_by_zero` is signalled.

  ## Examples

      iex> PackedDecimal.div_int(5, 2)
      #Decimal<2>

      iex> PackedDecimal.div_int("Inf", -1)
      #Decimal<-Infinity>

  """
  @spec div_int(decimal, decimal) :: t
  def div_int(binary_decimal(1) = num1, binary_decimal(2)) when nan1 == 1 do
    silence_unused(1); silence_unused(2)
    num1
  end

  def div_int(binary_decimal(1), binary_decimal(2) = num2) when nan2 == 1 do
    silence_unused(1); silence_unused(2)
    num2
  end

  def div_int(binary_decimal(1), binary_decimal(2)) when inf1 == 1 and inf2 == 1 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "±Infinity / ±Infinity", nan())
  end

  def div_int(binary_decimal(1) = num1, binary_decimal(2)) when inf1 == 1 do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: 0
    put_sign(num1, sign)
  end

  def div_int(binary_decimal(1), binary_decimal(2)) when inf2 == 1 do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: 0
    new(sign, _nan = 0, _inf = 0, exp1 - exp2, _coef = 0)
  end

  def div_int(binary_decimal(1), binary_decimal(2)) when coef1 == 0 and coef2 == 0 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "0 / 0", nan())
  end

  def div_int(binary_decimal(1), binary_decimal(2)) when coef2 == 0 do
    silence_unused(1); silence_unused(2)
    div_sign = if sign1 == sign2, do: 1, else: 0
    error(:division_by_zero, nil, infinity(div_sign))
  end

  def div_int(binary_decimal(1) = num1, binary_decimal(2) = num2) do
    silence_unused(1); silence_unused(2)
    div_sign = if sign1 == sign2, do: 1, else: -1

    cond do
      compare(put_sign(num1, 1), put_sign(num2, 1)) == :lt ->
        new(div_sign, _nan = 0, _inf = 0, exp1 - exp2, _coef: 0)

      coef1 == 0 ->
        context(put_sign(num1, div_sign))

      true ->
        case integer_division(div_sign, coef1, exp1, coef2, exp2) do
          {:ok, result} ->
            result

          {:error, error, reason, num} ->
            error(error, reason, num)
        end
    end
  end

  def div_int(num1, num2) do
    div_int(decimal(num1), decimal(num2))
  end

  @doc """
  Remainder of integer division of two numbers. The result will have the sign of
  the first number.

  ## Exceptional conditions

    * If both numbers are ±Infinity `:invalid_operation` is signalled.
    * If both numbers are ±0 `:invalid_operation` is signalled.
    * If second number (denominator) is ±0 `:division_by_zero` is signalled.

  ## Examples

      iex> Decimal.rem(5, 2)
      #Decimal<1>

  """
  @spec rem(decimal, decimal) :: t
  def rem(binary_decimal(1) = num1, binary_decimal(2)) when nan1 == 1 do
    silence_unused(1); silence_unused(2)
    num1
  end

  def rem(binary_decimal(1), binary_decimal(2) = num2) when nan2 == 1 do
    silence_unused(1); silence_unused(2)
    num2
  end

  def rem(binary_decimal(1), binary_decimal(2)) when inf1 == 1 and inf2 == 1 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "±Infinity / ±Infinity", nan())
  end

  def rem(binary_decimal(1), binary_decimal(2)) when inf1 == 1 do
    silence_unused(1); silence_unused(2)
    new(sign1, _nan = 0, _inf = 0, _exp = 0, _coef = 0)
  end

  def rem(binary_decimal(1), binary_decimal(2) = num2) when inf2 == 1 do
    silence_unused(1); silence_unused(2)
    # TODO: Subnormal
    # exponent?
    put_sign(num2, sign1)
  end

  def rem(binary_decimal(1), binary_decimal(2)) when coef1 == 0 and coef2 == 0 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "0 / 0", nan())
  end

  def rem(binary_decimal(1), binary_decimal(2)) when coef2 == 0 do
    silence_unused(1); silence_unused(2)
    error(:division_by_zero, nil, new(sign1, _nan = 0, _inf = 0, _exp = 0, _coef = 0))
  end

  def rem(binary_decimal(1), binary_decimal(2)) when coef2 == 0 do
    silence_unused(1); silence_unused(2)
    error(:division_by_zero, nil, new(sign1, _nan = 0, _inf = 0, _exp = 0, _coef = 0))
  end

  def rem(binary_decimal(1) = num1, binary_decimal(2) = num2) do
    silence_unused(1); silence_unused(2)

    cond do
      compare(put_sign(num1, 1), put_sign(num2, 1)) == :lt ->
        put_sign(num1, 1)

      coef1 == 0 ->
        context(put_sign(num2, sign1))

      true ->
        div_sign = if sign1 == sign2, do: 1, else: -1

        case integer_division(div_sign, coef1, exp1, coef2, exp2) do
          {:ok, result} ->
            sub(num1, mult(num2, result))

          {:error, error, reason, num} ->
            error(error, reason, num)
        end
    end
  end

  def rem(num1, num2) do
    rem(decimal(num1), decimal(num2))
  end
#
#   @doc """
#   Integer division of two numbers and the remainder. Should be used when both
#   `div_int/2` and `rem/2` is needed. Equivalent to: `{Decimal.div_int(x, y),
#   Decimal.rem(x, y)}`.
#
#   ## Exceptional conditions
#
#     * If both numbers are ±Infinity `:invalid_operation` is signalled.
#     * If both numbers are ±0 `:invalid_operation` is signalled.
#     * If second number (denominator) is ±0 `:division_by_zero` is signalled.
#
#   ## Examples
#
#       iex> Decimal.div_rem(5, 2)
#       {Decimal.new(2), Decimal.new(1)}
#
#   """
#   @spec div_rem(decimal, decimal) :: {t, t}
#   def div_rem(%Decimal{coef: :NaN} = num1, %Decimal{}), do: {num1, num1}
#
#   def div_rem(%Decimal{}, %Decimal{coef: :NaN} = num2), do: {num2, num2}
#
#   def div_rem(%Decimal{coef: :inf}, %Decimal{coef: :inf}) do
#     numbers = {%Decimal{coef: :NaN}, %Decimal{coef: :NaN}}
#     error(:invalid_operation, "±Infinity / ±Infinity", numbers)
#   end
#
#   def div_rem(%Decimal{sign: sign1, coef: :inf} = num1, %Decimal{sign: sign2}) do
#     sign = if sign1 == sign2, do: 1, else: -1
#     {%{num1 | sign: sign}, %Decimal{sign: sign1, coef: 0}}
#   end
#
#   def div_rem(%Decimal{} = num1, %Decimal{coef: :inf} = num2) do
#     %Decimal{sign: sign1, exp: exp1} = num1
#     %Decimal{sign: sign2, exp: exp2} = num2
#
#     sign = if sign1 == sign2, do: 1, else: -1
#     # TODO: Subnormal
#     # exponent?
#     {%Decimal{sign: sign, coef: 0, exp: exp1 - exp2}, %{num2 | sign: sign1}}
#   end
#
#   def div_rem(%Decimal{coef: 0}, %Decimal{coef: 0}) do
#     error = error(:invalid_operation, "0 / 0", %Decimal{coef: :NaN})
#     {error, error}
#   end
#
#   def div_rem(%Decimal{sign: sign1}, %Decimal{sign: sign2, coef: 0}) do
#     div_sign = if sign1 == sign2, do: 1, else: -1
#     div_error = error(:division_by_zero, nil, %Decimal{sign: div_sign, coef: :inf})
#     rem_error = error(:division_by_zero, nil, %Decimal{sign: sign1, coef: 0})
#     {div_error, rem_error}
#   end
#
#   def div_rem(%Decimal{} = num1, %Decimal{} = num2) do
#     %Decimal{sign: sign1, coef: coef1, exp: exp1} = num1
#     %Decimal{sign: sign2, coef: coef2, exp: exp2} = num2
#     div_sign = if sign1 == sign2, do: 1, else: -1
#
#     cond do
#       compare(%{num1 | sign: 1}, %{num2 | sign: 1}) == :lt ->
#         {%Decimal{sign: div_sign, coef: 0, exp: exp1 - exp2}, %{num1 | sign: sign1}}
#
#       coef1 == 0 ->
#         {context(%{num1 | sign: div_sign}), context(%{num2 | sign: sign1})}
#
#       true ->
#         case integer_division(div_sign, coef1, exp1, coef2, exp2) do
#           {:ok, result} ->
#             {result, sub(num1, mult(num2, result))}
#
#           {:error, error, reason, num} ->
#             error(error, reason, {num, num})
#         end
#     end
#   end
#
#   def div_rem(num1, num2) do
#     div_rem(decimal(num1), decimal(num2))
#   end
#
#   @doc """
#   Compares two values numerically and returns the maximum. Unlike most other
#   functions in `Decimal` if a number is NaN the result will be the other number.
#   Only if both numbers are NaN will NaN be returned.
#
#   ## Examples
#
#       iex> Decimal.max(1, "2.0")
#       #Decimal<2.0>
#
#       iex> Decimal.max(1, "NaN")
#       #Decimal<1>
#
#       iex> Decimal.max("NaN", "NaN")
#       #Decimal<NaN>
#
#   """
#   @spec max(decimal, decimal) :: t
#   def max(%Decimal{coef: :NaN}, %Decimal{} = num2), do: num2
#
#   def max(%Decimal{} = num1, %Decimal{coef: :NaN}), do: num1
#
#   def max(%Decimal{sign: sign1, exp: exp1} = num1, %Decimal{sign: sign2, exp: exp2} = num2) do
#     case compare(num1, num2) do
#       :lt ->
#         num2
#
#       :gt ->
#         num1
#
#       :eq ->
#         cond do
#           sign1 != sign2 ->
#             if sign1 == 1, do: num1, else: num2
#
#           sign1 == 1 ->
#             if exp1 > exp2, do: num1, else: num2
#
#           sign1 == -1 ->
#             if exp1 < exp2, do: num1, else: num2
#         end
#     end
#     |> context()
#   end
#
#   def max(num1, num2) do
#     max(decimal(num1), decimal(num2))
#   end
#
#   @doc """
#   Compares two values numerically and returns the minimum. Unlike most other
#   functions in `Decimal` if a number is NaN the result will be the other number.
#   Only if both numbers are NaN will NaN be returned.
#
#   ## Examples
#
#       iex> Decimal.min(1, "2.0")
#       #Decimal<1>
#
#       iex> Decimal.min(1, "NaN")
#       #Decimal<1>
#
#       iex> Decimal.min("NaN", "NaN")
#       #Decimal<NaN>
#
#   """
#   @spec min(decimal, decimal) :: t
#   def min(%Decimal{coef: :NaN}, %Decimal{} = num2), do: num2
#
#   def min(%Decimal{} = num1, %Decimal{coef: :NaN}), do: num1
#
#   def min(%Decimal{sign: sign1, exp: exp1} = num1, %Decimal{sign: sign2, exp: exp2} = num2) do
#     case compare(num1, num2) do
#       :lt ->
#         num1
#
#       :gt ->
#         num2
#
#       :eq ->
#         cond do
#           sign1 != sign2 ->
#             if sign1 == -1, do: num1, else: num2
#
#           sign1 == 1 ->
#             if exp1 < exp2, do: num1, else: num2
#
#           sign1 == -1 ->
#             if exp1 > exp2, do: num1, else: num2
#         end
#     end
#     |> context()
#   end
#
#   def min(num1, num2) do
#     min(decimal(num1), decimal(num2))
#   end
#
  @doc """
  Negates the given number.

  ## Examples

      iex> Decimal.negate(1)
      #Decimal<-1>

      iex> Decimal.negate("-Inf")
      #Decimal<Infinity>

  """

  @spec negate(decimal) :: t
  def negate(binary_decimal() = num) when nan == 1, do: (silence_unused(); num)
  def negate(binary_decimal() = num), do: (silence_unused(); context(put_sign(num, -sign)))
  def negate(num), do: negate(decimal(num))

  @doc """
  Applies the context to the given number rounding it to specified precision.
  """

  @spec apply_context(t) :: t
  def apply_context(binary_decimal() = num), do: (silence_unused(); context(num))

  @doc """
  Check if given number is positive
  """

  @spec positive?(t) :: boolean
  def positive?(binary_decimal()) when nan == 1, do: (silence_unused(); false)
  def positive?(binary_decimal()) when coef == 0, do: (silence_unused(); false)
  def positive?(binary_decimal()) when sign == 0, do: (silence_unused(); false)
  def positive?(binary_decimal()) when sign == 1, do: (silence_unused(); true)

  @doc """
  Check if given number is negative
  """

  @spec negative?(t) :: boolean
  def negative?(binary_decimal()) when nan == 1, do: (silence_unused(); false)
  def negative?(binary_decimal()) when coef == 0, do: (silence_unused(); false)
  def negative?(binary_decimal()) when sign == 1, do: (silence_unused(); false)
  def negative?(binary_decimal()) when sign == 0, do: (silence_unused(); true)

  @doc """
  Multiplies two numbers.

  ## Exceptional conditions

    * If one number is ±0 and the other is ±Infinity `:invalid_operation` is
      signalled.

  ## Examples

      iex> PackedDecimal.mult("0.5", 3)
      #Decimal<1.5>

      iex> PackedDecimal.mult("Inf", -1)
      #Decimal<-Infinity>

  """
  @spec mult(decimal, decimal) :: t
  def mult(binary_decimal(1) = num1, binary_decimal(2)) when nan1 == 1 do
    silence_unused(1); silence_unused(2)
    num1
  end

  def mult(binary_decimal(1), binary_decimal(2) = num2) when nan2 == 1 do
    silence_unused(1); silence_unused(2)
    num2
  end

  def mult(binary_decimal(1), binary_decimal(2)) when coef1 == 0 and inf2 == 1 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "0 * ±Infinity", nan())
  end

  def mult(binary_decimal(1), binary_decimal(2)) when inf1 == 1 and coef2 == 0 do
    silence_unused(1); silence_unused(2)
    error(:invalid_operation, "0 * ±Infinity", nan())
  end

  def mult(binary_decimal(1), binary_decimal(2)) when inf1 == 1 do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: -1
    # exponent?
    new(sign, _nan = 0, _inf = 1, exp1 + exp2, _coef = 0)
  end

  def mult(binary_decimal(1), binary_decimal(2)) when inf2 == 1 do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: -1
    # exponent?
    new(sign, _nan = 0, _inf = 1, exp1 + exp2, _coef = 0)
  end

  def mult(binary_decimal(1), binary_decimal(2)) do
    silence_unused(1); silence_unused(2)
    sign = if sign1 == sign2, do: 1, else: -1
    new(sign, _nan = 0, _inf = 0, exp1 + exp2, coef1 * coef2)
  end

  def mult(num1, num2) do
    mult(decimal(num1), decimal(num2))
  end

  @doc """
  Normalizes the given decimal: removes trailing zeros from coefficient while
  keeping the number numerically equivalent by increasing the exponent.

  ## Examples

      iex> PackedDecimal.normalize(Decimal.new("1.00"))
      #Decimal<1>

      iex> PackedDecimal.normalize(Decimal.new("1.01"))
      #Decimal<1.01>

  """

  @spec normalize(t) :: t
  def normalize(binary_decimal() = num) when nan == 1 do
    silence_unused()
    num
  end

  def normalize(binary_decimal()) when inf == 1 do
    silence_unused()

    # exponent?
    new(sign, nan, inf, _exp = 0, coef)
  end

  def normalize(binary_decimal()) do
    silence_unused()

    if coef == 0 do
      new(sign, nan, inf, _exp = 0, _coef = 0)
    else
      do_normalize(coef, exp)
      |> put_sign(sign)
      |> context()
    end
  end

  @doc """
  Rounds the given number to specified decimal places with the given strategy
  (default is to round to nearest one). If places is negative, at least that
  many digits to the left of the decimal point will be zero.

  See `PackedDecimal.Context` for more information about rounding algorithms.

  ## Examples

      iex> PackedDecimal.round("1.234")
      #Decimal<1>

      iex> PackedDecimal.round("1.234", 1)
      #Decimal<1.2>

  """
  @spec round(decimal, integer, rounding) :: t
  def round(num, places \\ 0, mode \\ :half_up)

  def round(binary_decimal() = num, _, _) when nan == 1 do
    silence_unused()
    num
  end

  def round(binary_decimal() = num, _, _) when inf == 1 do
    silence_unused()
    num
  end

  def round(binary_decimal() = num, n, mode) do
    silence_unused()
    binary_decimal() = normalize(num)
    silence_unused()
    digits = :erlang.integer_to_list(coef)
    target_exp = -n
    value = do_round(sign, digits, exp, target_exp, mode)
    context(value, [])
  end

  def round(num, n, mode) do
    round(decimal(num), n, mode)
  end

  @doc """
  Finds the square root.

  ## Examples

      iex> PackedDecimal.sqrt("100")
      #Decimal<10>

  """

  @spec sqrt(decimal) :: t
  def sqrt(binary_decimal() = num) when nan == 1 do
    silence_unused()
    error(:invalid_operation, "operation on NaN", num)
  end

  def sqrt(binary_decimal()) when exp == 1 do
    silence_unused()
    new(sign, nan, inf, exp >>> 1, coef)
  end

  def sqrt(binary_decimal() = num) when sign == 0 do
    silence_unused()
    error(:invalid_operation, "less than zero", num)
  end

  def sqrt(binary_decimal() = num) when inf == 1 do
    silence_unused()
    num
  end

  def sqrt(binary_decimal()) do
    silence_unused()
    precision = Context.get().precision + 1
    digits = :erlang.integer_to_list(coef)
    num_digits = length(digits)

    # Since the root is calculated from integer operations only, it must be
    # large enough to contain the desired precision. Calculate the amount of
    # `shift` required (powers of 10).
    case exp &&& 1 do
      0 ->
        # To get the desired `shift`, subtract the precision of `coef`'s square
        # root from the desired precision.
        #
        # If `coef` is 10_000, the root is 100 (3 digits of precision).
        # If `coef` is 100, the root is 10 (2 digits of precision).
        shift = precision - ((num_digits + 1) >>> 1)
        sqrt(coef, shift, exp)

      _ ->
        # If `exp` is odd, multiply `coef` by 10 and reduce shift by 1/2. `exp`
        # must be even so the root's exponent is an integer.
        shift = precision - ((num_digits >>> 1) + 1)
        sqrt(coef * 10, shift, exp)
    end
  end

  def sqrt(num) do
    sqrt(decimal(num))
  end

  defp sqrt(coef, shift, exp) do
    if shift >= 0 do
      # shift `coef` up by `shift * 2` digits
      sqrt(coef * pow10(shift <<< 1), shift, exp, true)
    else
      # shift `coef` down by `shift * 2` digits
      operand = pow10(-shift <<< 1)
      sqrt(Kernel.div(coef, operand), shift, exp, Kernel.rem(coef, operand) === 0)
    end
  end

  defp sqrt(shifted_coef, shift, exp, exact) do
    # the preferred exponent is `exp / 2` as per IEEE 754
    exp = exp >>> 1
    # guess a root 10x higher than desired precision
    guess = pow10(Context.get().precision + 1)
    root = sqrt_loop(shifted_coef, guess)

    if exact and root * root === shifted_coef do
      # if the root is exact, use preferred `exp` and shift `coef` to match
      coef =
        if shift >= 0,
          do: Kernel.div(root, pow10(shift)),
          else: root * pow10(-shift)

      context(new(_sign = 1, _nan = 0, _inf = 0, exp, coef))
    else
      # otherwise the calculated root is inexact (but still meets precision),
      # so use the root as `coef` and get the final exponent by shifting `exp`
      context(new(_sign = 1, _nan = 0, _inf = 0, exp - shift, _coef = root))
    end
  end

  # Babylonion method
  defp sqrt_loop(coef, guess) do
    quotient = Kernel.div(coef, guess)

    if guess <= quotient do
      guess
    else
      sqrt_loop(coef, (guess + quotient) >>> 1)
    end
  end

  @doc """
  Creates a new decimal number from an integer or a string representation.

  A decimal number will always be created exactly as specified with all digits
  kept - it will not be rounded with the context.

  ## Backus–Naur form

      sign           ::=  "+" | "-"
      digit          ::=  "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
      indicator      ::=  "e" | "E"
      digits         ::=  digit [digit]...
      decimal-part   ::=  digits "." [digits] | ["."] digits
      exponent-part  ::=  indicator [sign] digits
      infinity       ::=  "Infinity" | "Inf"
      nan            ::=  "NaN" [digits]
      numeric-value  ::=  decimal-part [exponent-part] | infinity
      numeric-string ::=  [sign] numeric-value | [sign] nan

  ## Floats

  See also `from_float/1`.

  ## Examples

      iex> PackedDecimal.new(1)
      #Decimal<1>

      iex> PackedDecimal.new("3.14")
      #Decimal<3.14>

  """
  @spec new(decimal) :: t
  def new(binary_decimal() = binary_decimal) do
    silence_unused()
    binary_decimal
  end

  def new(int) when is_integer(int) do
    if int in @min_int..@max_int do
      sign = if(int <= 0, do: 0, else: 1)
      coef = Kernel.abs(int)
      new(sign, _nan = 0, _inf = 0, _exp = 0, coef)
    else
      raise ArgumentError,
        "Integer must be between #{inspect @min_int}..#{inspect @max_int}. Found #{inspect int}"
    end
  end

  def new(binary) when is_binary(binary) do
    case parse(binary) do
      {binary_decimal, ""} -> binary_decimal
      _ -> raise Error, reason: "number parsing syntax: #{inspect(binary)}"
    end
  end

  @doc false
  def new(sign, nan, inf, exp, coef) do
    %__MODULE__{binary_decimal: pack(sign, nan, inf, exp, coef)}
  end

  @doc """
  Creates a new decimal number from the sign, coefficient and exponent such that
  the number will be: `sign * coefficient * 10 ^ exponent`.

  A decimal number will always be created exactly as specified with all digits
  kept - it will not be rounded with the context.
  """
  @spec new(1 | -1 | 0, non_neg_integer | :NaN | :inf, integer) :: t
  def new(sign, coef, exp)
      when sign in [1, -1, 0] and ((is_integer(coef) and coef >= 0)) and is_integer(exp) do
    new(sign, _nan = 0, _inf = 0, exp, coef)
  end

  def new(sign, :NaN, _exp) do
    nan(sign)
  end

  def new(sign, :inf, _exp) do
    infinity(sign)
  end

  @doc """
  Creates a new decimal number from a floating point number.

  Floating point numbers use a fixed number of binary digits to represent
  a decimal number which has inherent inaccuracy as some decimal numbers cannot
  be represented exactly in limited precision binary.

  Floating point numbers will be converted to decimal numbers with
  `:io_lib_format.fwrite_g/1`. Since this conversion is not exact and
  because of inherent inaccuracy mentioned above, we may run into counter-intuitive results:

      iex> Enum.reduce([0.1, 0.1, 0.1], &+/2)
      0.30000000000000004

      iex> Enum.reduce([PackedDecimal.new("0.1"), PackedDecimal.new("0.1"), PackedDecimal.new("0.1")], &PackedDecimal.add/2)
      #Decimal<0.3>

  For this reason, it's recommended to build decimals with `new/1`, which is always precise, instead.

  ## Examples

      iex> PackedDecimal.from_float(3.14)
      #Decimal<3.14>

  """

  @spec from_float(float) :: t
  def from_float(float) when is_float(float) do
    float
    |> :io_lib_format.fwrite_g()
    |> fix_float_exp()
    |> IO.iodata_to_binary()
    |> new()
  end

  @doc """
  Creates a new decimal number from an integer, string, float, or existing decimal number.

  Because conversion from a floating point number is not exact, it's recommended
  to instead use `new/1` or `from_float/1` when the argument's type is certain.
  See `from_float/1`.

  ## Examples

      iex> {:ok, binary_decimal} = PackedDecimal.cast(3)
      iex> binary_decimal
      #PackedDecimal<3>

      iex> PackedDecimal.cast("bad")
      :error

  """
  @spec cast(term) :: {:ok, t} | :error
  def cast(integer) when is_integer(integer), do: {:ok, new(integer)}
  def cast(binary_decimal() = binary_decimal), do: (silence_unused(); {:ok, binary_decimal})
  def cast(float) when is_float(float), do: {:ok, from_float(float)}

  def cast(binary) when is_binary(binary) do
    case parse(binary) do
      {binary_decimal, ""} -> {:ok, binary_decimal}
      _ -> :error
    end
  end

  def cast(_), do: :error

  @doc """
  Parses a binary into a decimal.

  If successful, returns a tuple in the form of `{decimal, remainder_of_binary}`,
  otherwise `:error`.

  ## Examples

      iex> PackedDecimal.parse("3.14")
      {%PackedDecimal{coef: 314, exp: -2, sign: 1}, ""}

      iex> Decimal.parse("3.14.15")
      {%PackedDecimal{coef: 314, exp: -2, sign: 1}, ".15"}

      iex> Decimal.parse("-1.1e3")
      {%PackedDecimal{coef: 11, exp: 2, sign: -1}, ""}

      iex> PackedDecimal.parse("bad")
      :error

  """
  @spec parse(binary()) :: {t(), binary()} | :error
  def parse("+" <> rest) do
    parse_unsign(rest)
  end

  def parse("-" <> rest) do
    case parse_unsign(rest) do
      {%__MODULE__{} = num, rest} -> {put_sign(num, 0), rest}
      :error -> :error
    end
  end

  def parse(binary) when is_binary(binary) do
    parse_unsign(binary)
  end

  @doc """
  Converts given number to its string representation.

  ## Options

    * `:scientific` - number converted to scientific notation.
    * `:normal` - number converted without a exponent.
    * `:xsd` - number converted to the [canonical XSD representation](https://www.w3.org/TR/xmlschema-2/#decimal).
    * `:raw` - number converted to its raw, internal format.

  """
  @spec to_string(t, :scientific | :normal | :xsd | :raw) :: String.t()
  def to_string(num, type \\ :scientific)

  def to_string(binary_decimal(), _type) when inf == 1 do
    silence_unused()
    if sign == 1, do: "Infinity", else: "-Infinity"
  end

  def to_string(binary_decimal(), :normal) do
    silence_unused()
    list = Integer.to_charlist(coef)

    list =
      if exp >= 0 do
        list ++ :lists.duplicate(exp, ?0)
      else
        diff = length(list) + exp

        if diff > 0 do
          List.insert_at(list, diff, ?.)
        else
          '0.' ++ :lists.duplicate(-diff, ?0) ++ list
        end
      end

    list = if sign == 0, do: [?- | list], else: list
    IO.iodata_to_binary(list)
  end

  def to_string(binary_decimal(), :scientific) do
    silence_unused()
    list = Integer.to_charlist(coef)
    length = length(list)
    adjusted = exp + length - 1

    list =
      cond do
        exp == 0 ->
          list

        exp < 0 and adjusted >= -6 ->
          abs_exp = Kernel.abs(exp)
          diff = -length + abs_exp + 1

          if diff > 0 do
            list = :lists.duplicate(diff, ?0) ++ list
            List.insert_at(list, 1, ?.)
          else
            List.insert_at(list, exp - 1, ?.)
          end

        true ->
          list = if length > 1, do: List.insert_at(list, 1, ?.), else: list
          list = list ++ 'E'
          list = if exp >= 0, do: list ++ '+', else: list
          list ++ Integer.to_charlist(adjusted)
      end

    list = if sign == 0, do: [?- | list], else: list
    IO.iodata_to_binary(list)
  end

  def to_string(binary_decimal(), :raw) do
    silence_unused()
    str = Integer.to_string(coef)
    str = if sign == 0, do: [?- | str], else: str
    str = if exp != 0, do: [str, "E", Integer.to_string(exp)], else: str

    IO.iodata_to_binary(str)
  end

  # def to_string(binary_decimal() = decimal, :xsd) do
  #   silence_unused()
  #   decimal |> canonical_xsd() |> to_string(:normal)
  # end
  #
  # defp canonical_xsd(%Decimal{coef: 0} = decimal), do: %{decimal | exp: -1}
  #
  # defp canonical_xsd(%Decimal{coef: coef, exp: 0} = decimal),
  #   do: %{decimal | coef: coef * 10, exp: -1}
  #
  # defp canonical_xsd(%Decimal{coef: coef, exp: exp} = decimal)
  #      when exp > 0,
  #      do: canonical_xsd(%{decimal | coef: coef * 10, exp: exp - 1})
  #
  # defp canonical_xsd(%Decimal{coef: coef} = decimal)
  #      when Kernel.rem(coef, 10) != 0,
  #      do: decimal
  #
  # defp canonical_xsd(%Decimal{coef: coef, exp: exp} = decimal),
  #   do: canonical_xsd(%{decimal | coef: Kernel.div(coef, 10), exp: exp + 1})

  @doc """
  Returns the decimal represented as an integer.

  Fails when loss of precision will occur.
  """
  @spec to_integer(t) :: integer
  def to_integer(binary_decimal()) when exp == 0 and nan == 0 and inf == 0 do
    sign(sign) * coef
  end

  def to_integer(binary_decimal()) when exp > 0 and nan == 0 and inf == 0 do
    new(sign, nan, inf, exp - 1, coef * 10)
    |> to_integer
  end

  def to_integer(binary_decimal())
      when exp < 0 and Kernel.rem(coef, 10) and nan == 0 and inf == 0 do
    new(sign, nan, inf, exp + 1, Kernel.div(coef, 10))
    |> to_integer
  end

  def to_integer(binary_decimal() = decimal) when is_integer(coef) do
    silence_unused()
    raise ArgumentError,
          "cannot convert #{inspect(decimal)} without losing precision. Use Decimal.round/3 first."
  end

  @doc """
  Returns the decimal converted to a float.

  The returned float may have lower precision than the decimal. Fails if
  the decimal cannot be converted to a float.
  """
  @spec to_float(t) :: float
  def to_float(binary_decimal()) when nan == 0 and inf == 0 do
    # Convert back to float without loss
    # http://www.exploringbinary.com/correct-decimal-to-floating-point-using-big-integers/
    {num, den} = ratio(coef, exp)

    boundary = den <<< 52

    cond do
      num == 0 ->
        0.0

      num >= boundary ->
        {den, exp} = scale_down(num, boundary, 52)
        decimal_to_float(sign, num, den, exp)

      true ->
        {num, exp} = scale_up(num, boundary, 52)
        decimal_to_float(sign, num, den, exp)
    end
  end

  defp scale_up(num, den, exp) when num >= den, do: {num, exp}
  defp scale_up(num, den, exp), do: scale_up(num <<< 1, den, exp - 1)

  defp scale_down(num, den, exp) do
    new_den = den <<< 1

    if num < new_den do
      {den >>> 52, exp}
    else
      scale_down(num, new_den, exp + 1)
    end
  end

  defp decimal_to_float(sign, num, den, exp) do
    quo = Kernel.div(num, den)
    rem = num - quo * den

    tmp =
      case den >>> 1 do
        den when rem > den -> quo + 1
        den when rem < den -> quo
        _ when (quo &&& 1) === 1 -> quo + 1
        _ -> quo
      end

    sign = if sign == -1, do: 1, else: 0
    tmp = tmp - @power_of_2_to_52
    exp = if tmp < @power_of_2_to_52, do: exp, else: exp + 1
    <<tmp::float>> = <<sign::size(1), exp + 1023::size(11), tmp::size(52)>>
    tmp
  end

  @doc """
  Returns `true` when the given `decimal` has no significant digits after the decimal point.

  ## Examples

      iex> PackedDecimal.integer?("1.00")
      true

      iex> PackedDecimal.integer?("1.10")
      false
  """

  @spec integer?(decimal()) :: boolean
  def integer?(binary_decimal()) when nan == 1, do: (silence_unused(); false)
  def integer?(binary_decimal()) when inf == 1, do: (silence_unused(); false)
  def integer?(binary_decimal()), do: (silence_unused(); exp >= 0 or zero_after_dot?(coef, exp))
  def integer?(num), do: integer?(decimal(num))

  defp zero_after_dot?(coef, exp) when coef >= 10 and exp < 0,
    do: Kernel.rem(coef, 10) == 0 and zero_after_dot?(Kernel.div(coef, 10), exp + 1)

  defp zero_after_dot?(_coef, exp),
    do: exp == 0

  ## ARITHMETIC ##

  defp add_align(coef1, exp1, coef2, exp2) when exp1 == exp2, do: {coef1, coef2}

  defp add_align(coef1, exp1, coef2, exp2) when exp1 > exp2,
    do: {coef1 * pow10(exp1 - exp2), coef2}

  defp add_align(coef1, exp1, coef2, exp2) when exp1 < exp2,
    do: {coef1, coef2 * pow10(exp2 - exp1)}

  defp add_sign(sign1, sign2, coef) do
    cond do
      coef > 0 -> 1
      coef < 0 -> -1
      sign1 == -1 and sign2 == -1 -> -1
      sign1 != sign2 and Context.get().rounding == :floor -> -1
      true -> 1
    end
  end

  defp div_adjust(coef1, coef2, adjust) when coef1 < coef2,
    do: div_adjust(coef1 * 10, coef2, adjust + 1)

  defp div_adjust(coef1, coef2, adjust) when coef1 >= coef2 * 10,
    do: div_adjust(coef1, coef2 * 10, adjust - 1)

  defp div_adjust(coef1, coef2, adjust), do: {coef1, coef2, adjust}

  defp div_calc(coef1, coef2, coef, adjust, prec10) do
    cond do
      coef1 >= coef2 ->
        div_calc(coef1 - coef2, coef2, coef + 1, adjust, prec10)

      coef1 == 0 and adjust >= 0 ->
        {coef, adjust, coef1, []}

      coef >= prec10 ->
        signals = [:rounded]
        signals = if base10?(coef1), do: signals, else: [:inexact | signals]
        {coef, adjust, coef1, signals}

      true ->
        div_calc(coef1 * 10, coef2, coef * 10, adjust + 1, prec10)
    end
  end

  defp div_int_calc(coef1, coef2, coef, adjust, precision) do
    cond do
      coef1 >= coef2 ->
        div_int_calc(coef1 - coef2, coef2, coef + 1, adjust, precision)

      adjust != precision ->
        div_int_calc(coef1 * 10, coef2, coef * 10, adjust + 1, precision)

      true ->
        {coef, coef1}
    end
  end

  defp integer_division(div_sign, coef1, exp1, coef2, exp2) do
    precision = exp1 - exp2
    {coef1, coef2, adjust} = div_adjust(coef1, coef2, 0)

    {coef, _rem} = div_int_calc(coef1, coef2, 0, adjust, precision)

    prec10 = pow10(Context.get().precision)

    if coef > prec10 do
      {
        :error,
        :invalid_operation,
        "integer division impossible, quotient too large",
        nan()
      }
    else
      {:ok, new(div_sign, _nan = 0, _inf = 0, _exp = 0, coef)}
    end
  end

  defp do_normalize(coef, exp) do
    if Kernel.rem(coef, 10) == 0 do
      do_normalize(Kernel.div(coef, 10), exp + 1)
    else
      {:ok, new(_sign = 1, _nan = 0, _inf = 0, exp, coef)}
    end
  end

  defp ratio(coef, exp) when exp >= 0, do: {coef * pow10(exp), 1}
  defp ratio(coef, exp) when exp < 0, do: {coef, pow10(-exp)}

  pow10_max =
    Enum.reduce(0..104, 1, fn int, acc ->
      defp pow10(unquote(int)), do: unquote(acc)
      defp base10?(unquote(acc)), do: true
      acc * 10
    end)

  defp pow10(num) when num > 104, do: pow10(104) * pow10(num - 104)

  defp base10?(num) when num >= unquote(pow10_max) do
    if Kernel.rem(num, unquote(pow10_max)) == 0 do
      base10?(Kernel.div(num, unquote(pow10_max)))
    else
      false
    end
  end

  defp base10?(_num), do: false

  ## ROUNDING ##

  defp do_round(sign, digits, exp, target_exp, rounding) do
    num_digits = length(digits)
    precision = num_digits - (target_exp - exp)

    cond do
      exp == target_exp ->
        new(sign, _nan = 0, _inf = 0, exp, digits_to_integer(digits))

      exp < target_exp and precision < 0 ->
        zeros = :lists.duplicate(target_exp - exp, ?0)
        digits = zeros ++ digits
        {signif, remain} = :lists.split(1, digits)

        signif =
          if increment?(rounding, sign, signif, remain),
            do: digits_increment(signif),
            else: signif

        coef = digits_to_integer(signif)
        new(sign, _nan = 0, _inf = 0, target_exp, coef)

      exp < target_exp and precision >= 0 ->
        {signif, remain} = :lists.split(precision, digits)

        signif =
          if increment?(rounding, sign, signif, remain),
            do: digits_increment(signif),
            else: signif

        coef = digits_to_integer(signif)
        new(sign, _nan = 0, _inf = 0, target_exp, coef)

      exp > target_exp ->
        digits = digits ++ Enum.map(1..(exp - target_exp), fn _ -> ?0 end)
        coef = digits_to_integer(digits)
        new(sign, _nan = 0, _inf = 0, target_exp, coef)
    end
  end

  defp digits_to_integer([]), do: 0
  defp digits_to_integer(digits), do: :erlang.list_to_integer(digits)

  defp precision(binary_decimal() = num, _precision, _rounding) when nan == 1 do
    silence_unused()
    {num, []}
  end

  defp precision(binary_decimal() = num, _precision, _rounding) when inf == 1 do
    silence_unused()
    {num, []}
  end

  defp precision(binary_decimal() = num, precision, rounding) do
    silence_unused()
    digits = :erlang.integer_to_list(coef)
    num_digits = length(digits)

    if num_digits > precision do
      do_precision(sign, digits, num_digits, exp, precision, rounding)
    else
      {num, []}
    end
  end

  defp do_precision(sign, digits, num_digits, exp, precision, rounding) do
    precision = Kernel.min(num_digits, precision)
    {signif, remain} = :lists.split(precision, digits)

    signif =
      if increment?(rounding, sign, signif, remain), do: digits_increment(signif), else: signif

    signals = if any_nonzero(remain), do: [:inexact, :rounded], else: [:rounded]

    exp = exp + length(remain)
    coef = digits_to_integer(signif)
    dec = new(sign, _nan = 0, _inf = 0, exp, coef)
    {dec, signals}
  end

  defp increment?(_, _, _, []), do: false

  defp increment?(:down, _, _, _), do: false

  defp increment?(:up, _, _, _), do: true

  defp increment?(:ceiling, sign, _, remain), do: sign == 1 and any_nonzero(remain)

  defp increment?(:floor, sign, _, remain), do: sign == -1 and any_nonzero(remain)

  defp increment?(:half_up, _, _, [digit | _]), do: digit >= ?5

  defp increment?(:half_even, _, [], [?5 | rest]), do: any_nonzero(rest)

  defp increment?(:half_even, _, signif, [?5 | rest]),
    do: any_nonzero(rest) or Kernel.rem(:lists.last(signif), 2) == 1

  defp increment?(:half_even, _, _, [digit | _]), do: digit > ?5

  defp increment?(:half_down, _, _, [digit | rest]),
    do: digit > ?5 or (digit == ?5 and any_nonzero(rest))

  defp any_nonzero(digits), do: :lists.any(fn digit -> digit != ?0 end, digits)

  defp digits_increment(digits), do: digits_increment(:lists.reverse(digits), [])

  defp digits_increment([?9 | rest], acc), do: digits_increment(rest, [?0 | acc])

  defp digits_increment([head | rest], acc), do: :lists.reverse(rest, [head + 1 | acc])

  defp digits_increment([], acc), do: [?1 | acc]
#
#   ## CONTEXT ##

  defp context(num, signals \\ []) do
    context = Context.get()
    {result, prec_signals} = precision(num, context.precision, context.rounding)
    error(put_uniq(signals, prec_signals), nil, result, context)
  end

  defp put_uniq(list, elems) when is_list(elems) do
    Enum.reduce(elems, list, &put_uniq(&2, &1))
  end

  defp put_uniq(list, elem) do
    if elem in list, do: list, else: [elem | list]
  end

  ## PARSING ##

  defp parse_unsign(<<first, remainder::size(7)-binary, rest::binary>>) when first in [?i, ?I] do
    if String.downcase(remainder) == "nfinity" do
      {infinity(), rest}
    else
      :error
    end
  end

  defp parse_unsign(<<first, remainder::size(2)-binary, rest::binary>>) when first in [?i, ?I] do
    if String.downcase(remainder) == "nf" do
      {infinity(), rest}
    else
      :error
    end
  end

  defp parse_unsign(<<first, remainder::size(2)-binary, rest::binary>>) when first in [?n, ?N] do
    if String.downcase(remainder) == "an" do
      {nan(), rest}
    else
      :error
    end
  end

  defp parse_unsign(bin) do
    {int, rest} = parse_digits(bin)
    {float, rest} = parse_float(rest)
    {exp, rest} = parse_exp(rest)

    if int == [] and float == [] do
      :error
    else
      int = if int == [], do: '0', else: int
      exp = if exp == [], do: '0', else: exp

      coef = List.to_integer(int ++ float)
      exp =  List.to_integer(exp) - length(float)
      number = new(_sign = 1, _nan = 0, _inf = 0, exp, coef)

      {number, rest}
    end
  end

  defp parse_float("." <> rest), do: parse_digits(rest)
  defp parse_float(bin), do: {[], bin}

  defp parse_exp(<<e, rest::binary>>) when e in [?e, ?E] do
    case rest do
      <<sign, rest::binary>> when sign in [?+, ?-] ->
        {digits, rest} = parse_digits(rest)
        {[sign | digits], rest}

      _ ->
        parse_digits(rest)
    end
  end

  defp parse_exp(bin) do
    {[], bin}
  end

  defp parse_digits(bin), do: parse_digits(bin, [])

  defp parse_digits(<<digit, rest::binary>>, acc) when digit in ?0..?9 do
    parse_digits(rest, [digit | acc])
  end

  defp parse_digits(rest, acc) do
    {:lists.reverse(acc), rest}
  end

  # Util

  defp decimal(%__MODULE__{} = num), do: num
  defp decimal(num) when is_integer(num), do: new(num)
  defp decimal(num) when is_binary(num), do: new(num)

  defp decimal(other) when is_float(other) do
    raise ArgumentError,
          "implicit conversion of #{inspect(other)} to PackedDecimal is not allowed. Use PackedDecimal.from_float/1"
  end

  defp handle_error(signals, reason, result, context) do
    context = context || Context.get()
    signals = List.wrap(signals)

    flags = Enum.reduce(signals, context.flags, &put_uniq(&2, &1))
    Context.set(%{context | flags: flags})
    error_signal = Enum.find(signals, &(&1 in context.traps))

    if error_signal do
      error = [signal: error_signal, reason: reason]
      {:error, error}
    else
      {:ok, result}
    end
  end

  defp fix_float_exp(digits) do
    fix_float_exp(digits, [])
  end

  defp fix_float_exp([?e | rest], [?0 | [?. | result]]) do
    fix_float_exp(rest, [?e | result])
  end

  defp fix_float_exp([digit | rest], result) do
    fix_float_exp(rest, [digit | result])
  end

  defp fix_float_exp([], result), do: :lists.reverse(result)

  defp put_sign({:ok, num}, sign) do
    put_sign(num, sign)
  end

  defp put_sign(binary_decimal(), sign) do
    silence_unused()
    sign = if(sign <= 0, do: 0, else: 1)
    new(sign, _nan = 0, _inf = 0, exp, coef)
  end
end

defimpl Inspect, for: BitstringDecimal do
  def inspect(dec, _opts) do
    "#BitstringDecimal<" <> BitstringDecimal.to_string(dec) <> ">"
  end
end

defimpl String.Chars, for: BitstringDecimal do
  def to_string(dec) do
    BitstringDecimal.to_string(dec)
  end
end
