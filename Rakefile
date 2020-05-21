# frozen_string_literal: true

require 'pathname'

desc 'generate AST graphs for all examples'
task :graphs, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    dot = mc.sub_ext('.dot')
    svg = mc.sub_ext('.svg')
    sh 'cargo', 'run', '--bin', 'mc_ast_to_dot', '--', '-o', dot.to_s, mc.to_s
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
task :symbol_tables, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    txt = mc.sub_ext('.txt')
    sh 'cargo', 'run', '--bin', 'mc_symbol_table', '--', '-o', txt.to_s, mc.to_s
  end
end

desc 'generate IR for all examples'
task :ir, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    ir = mc.sub_ext('.ir')
    sh 'cargo', 'run', '--bin', 'mc_ir', '--', '-o', ir.to_s, mc.to_s
  end
end

desc 'generate ASM for all examples'
task :asm, [:example] do |example: '*'|
  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.mc").each do |mc|
    asm = mc.sub_ext('.s')
    sh 'cargo', 'run', '--bin', 'mc_asm', '--', '-o', asm.to_s, mc.to_s
  end
end

desc 'compile and run all examples'
task :run, [:example] => :asm do |example: '*'|
  sh 'docker', 'build', '-t', 'gcc', '-f', 'Dockerfile.gcc', '.'

  Pathname.glob("#{__dir__}/examples/#{example}/#{example}.s").each do |asm|
    bin = asm.sub_ext('.bin')
    sh 'docker', 'run', '--rm', '-it', '-v', "#{__dir__}:#{__dir__}", '-w', __dir__, 'gcc', 'gcc', '-m32', asm.to_s, '-o', bin.to_s
    sh 'docker', 'run', '--rm', '-it', '-v', "#{__dir__}:#{__dir__}", '-w', __dir__, 'gcc', bin.to_s
  end
end
