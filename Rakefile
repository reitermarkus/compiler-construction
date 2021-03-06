# frozen_string_literal: true

require 'English'
require 'pathname'
require 'open3'

def cargo_run(*args)
  command, *args = args
  sh 'cargo', 'run', '--bin', command, '--', *args
end

def dot_to_svg(dot, svg)
  sh 'dot', '-T', 'svg', '-o', svg.to_s, dot.to_s

  begin
    sh 'sed', '-i', '', '-E', 's/\s*(height|width)="[^"]+"\s*/ /g', svg.to_s
    sh 'svgcleaner', svg.to_s, svg.to_s
    sh 'xmllint', '--format', svg.to_s, '-o', svg.to_s
  rescue RuntimeError
    # Ignore optional commands failing.
  end
end

desc 'generate AST graphs for all examples'
task :ast, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    dot = mc.sub_ext('.ast.dot')
    svg = mc.sub_ext('.ast.svg')
    cargo_run 'mc_ast_to_dot', '-o', dot.to_s, mc.to_s
    dot_to_svg(dot, svg)
  end
end

desc 'generate Symbol Tables for all examples'
task :symbol_table, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    txt = mc.sub_ext('.txt')
    cargo_run 'mc_symbol_table', '-o', txt.to_s, mc.to_s
  end
end

desc 'show error output for failing examples'
task :failures, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/faliures/#{example}.mc").each do |mc|
    txt = mc.sub_ext('.txt')
    begin
      cargo_run 'mc_symbol_table', '-o', txt.to_s, mc.to_s
      raise StandardError, 'This example should have raised an error!'
    rescue RuntimeError => e
      puts 'Errors received. Test passed!'
    end
  end
end

desc 'generate IR for all examples'
task :ir, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    ir = mc.sub_ext('.ir')
    cargo_run 'mc_ir', '-o', ir.to_s, mc.to_s
  end
end

desc 'generate CFG for all examples'
task :cfg, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    cfg = mc.sub_ext('.cfg.dot')
    svg = mc.sub_ext('.cfg.svg')
    cargo_run 'mc_cfg_to_dot', '-o', cfg.to_s, mc.to_s
    dot_to_svg(cfg, svg)
  end
end

desc 'generate ASM for all examples'
task :asm, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    asm = mc.sub_ext('.s')
    cargo_run 'mc_asm', '-o', asm.to_s, mc.to_s
  end
end

desc 'compile all examples'
task :compile, [:example] => [:build_ubuntu_docker_image] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    bin = mc.sub_ext('.bin')

    cargo_run 'mcc', mc.to_s, '-o', bin.to_s
  end
end

def run_example(mc, tty: false)
  dir = Pathname.pwd
  mc = Pathname(mc).relative_path_from(dir)
  bin = mc.sub_ext('.bin')

  if docker_image = ENV['MCC_DOCKER_IMAGE']
    ['docker', 'run', '--rm', '-i', *(tty ? '-t' : nil ), '-v', "#{dir}:/project", '-w', '/project', docker_image, "./#{bin}"]
  else
    ["./#{bin}"]
  end
end

desc 'run all examples'
task :run, [:example] => [:build_ubuntu_docker_image, :compile] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    system *run_example(mc, tty: STDIN.tty?)
    exit($CHILD_STATUS.exitstatus) unless $CHILD_STATUS.success?
  end
end

desc 'test all examples'
task :test, [:example] => [:build_ubuntu_docker_image, :compile] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    example_name = mc.sub_ext('').basename

    inputs = Pathname.glob(mc.sub_ext('.stdin*.txt')).sort
    expected_outputs = Pathname.glob(mc.sub_ext('.stdout*.txt')).sort

    raise "No IO tests found for example '#{example_name}'." if inputs.empty?

    inputs.zip(expected_outputs).each_with_index do |(input_file, expected_output_file), i|
      input = File.read(input_file)
      expected_output = File.read(expected_output_file)

      Open3.popen3(*run_example(mc)) do |stdin, stdout, stderr, wait_thr|
        stdin.write input
        stdin.close

        actual_output = stdout.read
        stdout.close
        stderr.close

        exit_status = wait_thr.value

        if exit_status.success?
          puts "Example '#{example_name}' passed IO test #{i + 1}."
        else
          raise "Example '#{example_name}' failed with status #{exit_status.exitstatus}"
        end

        next if actual_output == expected_output

        message = +"Example '#{example_name}' failed with wrong output. Expected output is\n"
        message << '─' * 100 << "\n"
        message << expected_output
        message << '─' * 100 << "\n"
        message << "but actual output was\n"
        message << '─' * 100 << "\n"
        message << actual_output
        message << '─' * 100 << "\n"

        raise message
      end
    end
  end
end

desc 'build Ubuntu 20.04 Docker image'
task :build_ubuntu_docker_image do
  begin
    stdout, *_ = Open3.capture3('lsb_release', '-a')
    next if stdout.match?(/\bUbuntu\s+20.04\b/)
  rescue Errno::ENOENT
    # Ignore.
  end

  ENV['MCC_DOCKER_IMAGE'] = 'reitermarkus/gcc-multilib'
  sh 'docker', 'build', '-t', ENV['MCC_DOCKER_IMAGE'], '-f', 'Dockerfile.gcc', '.'
end

desc 'clean example directories'
task :clean, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    FileUtils.rm_f mc.sub_ext('.dot')
    FileUtils.rm_f mc.sub_ext('.svg')
    FileUtils.rm_f mc.sub_ext('.txt')
    FileUtils.rm_f mc.sub_ext('.ir')
    FileUtils.rm_f mc.sub_ext('.s')
    FileUtils.rm_f mc.sub_ext('.bin')
  end
end
