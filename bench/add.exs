Benchee.run(
  %{
    "Decimal" => fn -> Decimal.add(100, 200) end,
    "Packed Decimal" => fn -> PackedDecimal.add(100, 200) end,
    "Bitstring Decimal" => fn -> BitstringDecimal.add(100, 200) end,
  },
  time: 10,
  memory_time: 2
)