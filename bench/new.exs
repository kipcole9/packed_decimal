Benchee.run(
  %{
    "Decimal" => fn -> Decimal.new(10) end,
    "Packed Decimal" => fn -> PackedDecimal.new(10) end,
  },
  time: 10,
  memory_time: 2
)