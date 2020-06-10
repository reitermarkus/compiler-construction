# frozen_string_literal: true

require 'English'
require 'pathname'
require 'open3'

def cargo_run(*args)
  command, *args = args
  sh 'cargo', 'run', '--bin', command, '--', *args
end

desc 'generate AST graphs for all examples'
task :graphs, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    dot = mc.sub_ext('.dot')
    svg = mc.sub_ext('.svg')
    cargo_run 'mc_ast_to_dot', '-o', dot.to_s, mc.to_s
    sh 'dot', '-T', 'svg', '-o', svg.to_s, dot.to_s

    begin
      sh 'sed', '-i', '', '-E', 's/\s*(height|width)="[^"]+"\s*/ /g', svg.to_s
      sh 'svgcleaner', svg.to_s, svg.to_s
      sh 'xmllint', '--format', svg.to_s, '-o', svg.to_s
    rescue RuntimeError
      # Ignore optional commands failing.
    end
  end
end

desc 'generate Symbol Tables for all examples'
task :symbol_table, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    txt = mc.sub_ext('.txt')
    cargo_run 'mc_symbol_table', '-o', txt.to_s, mc.to_s
  end
end

desc 'generate IR for all examples'
task :ir, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    ir = mc.sub_ext('.ir')
    cargo_run 'mc_ir', '-o', ir.to_s, mc.to_s
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
task :compile, [:example] => [:build_gcc_docker_image] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    dir = Pathname.pwd
    mc = Pathname(mc).relative_path_from(dir)
    bin = mc.sub_ext('.bin')

    cargo_run 'mcc', mc.to_s, '-o', bin.to_s
  end
end

def run_example(mc, tty: false)
  dir = Pathname.pwd
  mc = Pathname(mc).relative_path_from(dir)
  bin = mc.sub_ext('.bin')
  ['docker', 'run', '--rm', '-i', *(tty ? '-t' : nil ), '-v', "#{dir}:/project", '-w', '/project', ENV['MCC_DOCKER_IMAGE'], "./#{bin}"]
end

desc 'run all examples'
task :run, [:example] => [:build_gcc_docker_image, :compile] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    sh *run_example(mc, tty: STDIN.tty?)
  end
end

desc 'test all examples'
task :test, [:example] => [:build_gcc_docker_image, :compile] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    input = File.read(mc.sub_ext('.stdin.txt'))
    expected_output = File.read(mc.sub_ext('.stdout.txt'))

    Open3.popen3(*run_example(mc)) do |stdin, stdout, stderr, wait_thr|
      stdin.write input
      stdin.close

      exit_status = wait_thr.value

      unless exit_status.success?
        $stderr.puts "Example '#{mc.sub_ext('').basename}' failed with status #{exit_status.exitstatus}"
      end

      actual_output = stdout.read

      next if actual_output == expected_output

      $stderr.puts 'Expected:'
      $stderr.puts '─' * 100
      $stderr.puts expected_output
      $stderr.puts '─' * 100
      $stderr.puts 'Actual:'
      $stderr.puts '─' * 100
      $stderr.puts actual_output
      $stderr.puts '─' * 100
    end
  end
end

desc 'build GCC Docker image'
task :build_gcc_docker_image do
  ENV['MCC_DOCKER_IMAGE'] = 'gcc'
  sh 'docker', 'build', '-t', ENV['MCC_DOCKER_IMAGE'], '-f', 'Dockerfile.gcc', '.'
end
