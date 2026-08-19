# frozen_string_literal: true

require "minitest/autorun"
require "open3"
require "pathname"
require "rbconfig"
require "tempfile"

require_relative "../scripts/validate-formalization"

class ValidateFormalizationTest < Minitest::Test
  ROOT = Pathname(__dir__).parent
  SCRIPT = ROOT / "scripts/validate-formalization.rb"

  CUSTOMIZED_YAML = <<~YAML
    version: v0.4
    project:
      name: Example
      description: A concise account of the example result.
      license: Apache-2.0
    classification:
      arxiv: [math.LO]
      msc2020: [03B35]
    automation:
      methods:
        - method: manual
    review:
      status: self-assessed
  YAML

  def metadata(contents)
    Tempfile.create(["formalization", ".yaml"]) do |file|
      file.binmode
      file.write(contents)
      file.flush
      return yield file.path
    end
  end

  def cli(*arguments)
    Open3.capture3(RbConfig.ruby, SCRIPT.to_s, *arguments)
  end

  def test_accepts_customized_yaml
    metadata(CUSTOMIZED_YAML) do |path|
      assert_empty FormalizationTemplate.validate(path)
    end
  end

  def test_requires_v0_4
    metadata(CUSTOMIZED_YAML.sub("version: v0.4", "version: v0.3")) do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, '$.version must be "v0.4", not "v0.3"'
    end
  end

  def test_requires_the_apache_2_license_contract
    metadata(CUSTOMIZED_YAML.sub("license: Apache-2.0", "license: MIT")) do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, "$.project.license must be \"Apache-2.0\", not \"MIT\""
      assert_includes error.message, "Keep the repository's Apache-2.0 LICENSE file unchanged"
    end

    metadata(CUSTOMIZED_YAML.sub("  license: Apache-2.0\n", "")) do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, "$.project.license must be \"Apache-2.0\", not nil"
    end
  end

  def test_requires_a_bounded_public_description
    metadata(CUSTOMIZED_YAML.sub("  description: A concise account of the example result.\n", "")) do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, "$.project.description must be nonempty text"
    end
  end

  def test_cli_rejects_a_different_or_missing_root_license
    cases = {
      '"MIT"' => CUSTOMIZED_YAML.sub("license: Apache-2.0", "license: MIT"),
      "nil" => CUSTOMIZED_YAML.sub("  license: Apache-2.0\n", "")
    }
    cases.each do |actual, contents|
      metadata(contents) do |path|
        output, errors, status = cli(path)
        refute_predicate status, :success?
        assert_equal 1, status.exitstatus
        assert_empty output
        assert_includes errors,
                        "$.project.license must be \"Apache-2.0\", not #{actual}"
      end
    end
  end

  def test_reports_placeholders_inside_arrays_of_mappings
    document = {
      "sources" => [
        {
          "authors" => [{"name" => "TEMPLATE: source author"}],
          "contributors" => [
            {"name" => "TEMPLATE: editor", "role" => "TEMPLATE: editor role"}
          ]
        }
      ]
    }
    assert_equal [
      "$.sources[0].authors[0].name",
      "$.sources[0].contributors[0].name",
      "$.sources[0].contributors[0].role"
    ],
                 FormalizationTemplate.placeholder_paths(document)
  end

  def test_sentinel_is_anchored_and_accepts_bare_or_colon_forms
    document = {
      "values" => [
        "TEMPLATE",
        "TEMPLATE: replace me",
        "  TEMPLATE: replace me too",
        "TEMPLATES are useful",
        "prefix TEMPLATE: is ordinary text",
        "template: is case-sensitive"
      ]
    }
    assert_equal ["$.values[0]", "$.values[1]", "$.values[2]"],
                 FormalizationTemplate.placeholder_paths(document)
  end

  def test_requires_a_yaml_mapping
    metadata("- not\n- a\n- mapping\n") do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, "one top-level mapping"
    end
  end

  def test_requires_all_metadata_sections
    metadata("project: {}\nclassification: {}\n") do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, "required mapping sections: automation, review"
    end
  end

  def test_rejects_invalid_yaml
    metadata("project: [unterminated\n") do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, "cannot parse"
    end
  end

  def test_rejects_invalid_utf8_before_parsing
    metadata("project: \xFF\n".b) do |path|
      error = assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.validate(path)
      end
      assert_includes error.message, "must be valid UTF-8"
    end
  end

  def test_wraps_system_call_errors
    error = File.stub(:binread, ->(_path) { raise Errno::EACCES, "denied" }) do
      assert_raises(FormalizationTemplate::ValidationError) do
        FormalizationTemplate.load_document("unreadable.yaml")
      end
    end
    assert_includes error.message, "cannot read unreadable.yaml"
  end

  def test_derived_cli_succeeds_only_without_sentinels
    metadata(CUSTOMIZED_YAML) do |path|
      output, errors, status = cli(path)
      assert_predicate status, :success?
      assert_equal "#{path} contains no TEMPLATE values\n", output
      assert_empty errors
    end

    metadata(CUSTOMIZED_YAML.sub("Example", '"TEMPLATE: project name"')) do |path|
      output, errors, status = cli(path)
      refute_predicate status, :success?
      assert_equal 1, status.exitstatus
      assert_empty output
      assert_includes errors, "still contains 1 TEMPLATE value(s)"
      assert_includes errors, "$.project.name"
    end
  end

  # The canonical-only workflow is the integration test for the shipped
  # formalization.yaml. Unit tests must stay independent of that file because
  # repositories created from this template are required to customize it.
  def test_template_cli_rejects_a_non_template_surface
    metadata(CUSTOMIZED_YAML) do |path|
      output, errors, status = cli("--expect-template", path)
      refute_predicate status, :success?
      assert_equal 1, status.exitstatus
      assert_empty output
      assert_includes errors, "does not have the expected TEMPLATE sentinel surface"
      assert_includes errors, "missing expected values: $.project.name"
    end

    metadata("project: [unterminated\n") do |path|
      output, errors, status = cli("--expect-template", path)
      refute_predicate status, :success?
      assert_equal 1, status.exitstatus
      assert_empty output
      assert_includes errors, "cannot parse #{path} as YAML"
    end
  end

  def test_cli_reports_usage_errors_separately
    output, errors, status = cli("--not-an-option")
    refute_predicate status, :success?
    assert_equal 2, status.exitstatus
    assert_empty output
    assert_includes errors, "invalid option: --not-an-option"
    assert_includes errors, "Usage:"
  end
end

class MetadataWorkflowRoutingTest < Minitest::Test
  WORKFLOW = File.read(Pathname(__dir__).parent / ".github/workflows/ci.yml")
  CONDITIONS = WORKFLOW.lines.map(&:strip).grep(/\Aif:/).freeze

  def test_only_the_canonical_repository_uses_template_mode
    assert_includes CONDITIONS,
                    "if: github.repository == 'PalomarRegistry/EulerBrick'"
    assert_includes CONDITIONS,
                    "if: github.repository != 'PalomarRegistry/EulerBrick'"
  end
end
