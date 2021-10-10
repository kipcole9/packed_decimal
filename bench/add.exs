decimal = Decimal.new(10)
packed_decimal = PackedDecimal.new(10)

Benchee.run(
  %{
    "Decimal" => fn -> Decimal.add(decimal, decimal) end,
    "Packed Decimal" => fn -> PackedDecimal.add(packed_decimal, packed_decimal) end,
  },
  time: 10,
  memory_time: 2
)