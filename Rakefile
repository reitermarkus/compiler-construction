# frozen_string_literal: true

require 'pathname'

task :graphs do
  Pathname.glob("#{__dir__}/examples/*/*.mc").each do |mc|
    dot = mc.sub_ext('.dot')
    svg = mc.sub_ext('.svg')
    sh 'cargo', 'run', '--bin', 'mc_ast_to_dot', '--', '-o', dot.to_s, mc.to_s
    sh 'dot', '-T', 'svg', '-o', svg.to_s, dot.to_s
    sh 'svgcleaner', svg.to_s, svg.to_s
    sh 'xmllint', '--format', svg.to_s, '-o', svg.to_s
  end
end
