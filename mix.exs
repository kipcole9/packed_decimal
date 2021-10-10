defmodule PackedDecimal.Mixfile do
  use Mix.Project

  @version "0.1.0"
  @source_url "https://github.com/kipcole9/packed_decimal"

  def project() do
    [
      app: :packed_decimal,
      version: @version,
      elixir: "~> 1.10",
      deps: deps(),
      name: "Packed Decimal",
      source_url: @source_url,
      docs: [source_ref: "v#{@version}", main: "readme", extras: ["README.md"]],
      description: description(),
      package: package()
    ]
  end

  def application() do
    []
  end

  defp deps() do
    [
      {:ex_doc, ">= 0.0.0", only: :dev, runtime: false},
      {:decimal, "~> 2.0", optional: true},
      {:benchee, "~> 1.0"}
    ]
  end

  defp description() do
    "Fixed precision decimal arithmetic modelled after Decimal."
  end

  defp package() do
    [
      maintainers: ["Kip Cole"],
      licenses: ["Apache-2.0"],
      links: %{"GitHub" => @source_url}
    ]
  end
end
