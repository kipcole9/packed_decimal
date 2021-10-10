range = 1..1000

Benchee.run(
  %{
    "Decimal" => fn -> Enum.map(range, &Decimal.new/1) end,
    "Packed Decimal" => fn -> Enum.map(range, &PackedDecimal.new/1) end,
  },
  time: 10,
  memory_time: 2
)