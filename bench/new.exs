Benchee.run(
  %{
    "Decimal" => fn -> Decimal.new(10) end,
    "Packed Decimal" => fn -> PackedDecimal.new(10) end,
    "Bitstring Decimal" => fn -> BitstringDecimal.new(10) end,
  },
  time: 20,
  memory_time: 4
)