(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
(set-info :source |
MathSat group

|)
(set-info :category "random")
(set-info :status unsat)
(declare-fun f0_1 (Real) Real)
(declare-fun f0_2 (Real Real) Real)
(declare-fun f0_3 (Real Real Real) Real)
(declare-fun f0_4 (Real Real Real Real) Real)
(declare-fun f1_1 (Real) Real)
(declare-fun f1_2 (Real Real) Real)
(declare-fun f1_3 (Real Real Real) Real)
(declare-fun f1_4 (Real Real Real Real) Real)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun x7 () Real)
(declare-fun x8 () Real)
(declare-fun x9 () Real)
(declare-fun x10 () Real)
(declare-fun x11 () Real)
(declare-fun x12 () Real)
(declare-fun x13 () Real)
(declare-fun x14 () Real)
(declare-fun x15 () Real)
(declare-fun x16 () Real)
(declare-fun x17 () Real)
(declare-fun x18 () Real)
(declare-fun x19 () Real)
(declare-fun P0 () Bool)
(declare-fun P1 () Bool)
(declare-fun P2 () Bool)
(declare-fun P3 () Bool)
(declare-fun P4 () Bool)
(declare-fun P5 () Bool)
(declare-fun P6 () Bool)
(declare-fun P7 () Bool)
(declare-fun P8 () Bool)
(declare-fun P9 () Bool)
(declare-fun P10 () Bool)
(declare-fun P11 () Bool)
(declare-fun P12 () Bool)
(declare-fun P13 () Bool)
(declare-fun P14 () Bool)
(declare-fun P15 () Bool)
(declare-fun P16 () Bool)
(declare-fun P17 () Bool)
(declare-fun P18 () Bool)
(declare-fun P19 () Bool)
(assert (let ((?v_26 (f1_2 x5 x3)) (?v_202 (f0_1 x2)) (?v_117 (+ (- (* 22 x19) (* 20 x14)) (* 18 x13))) (?v_45 (f0_1 x3)) (?v_55 (- (- (* 24 x14) (* 7 x17)) (* 28 x10)))) (let ((?v_56 (f1_2 ?v_202 x2)) (?v_63 (- (+ (* 18 x3) (* 12 x11)) (* 2 x5))) (?v_95 (f0_2 x9 x1)) (?v_61 (* 27 x10)) (?v_53 (f1_2 x15 x1)) (?v_13 (f0_2 (f1_2 x9 x11) x1)) (?v_75 (- (+ (* 3 x2) (* 17 x16)) (* 16 x0))) (?v_142 (< ?v_26 22)) (?v_84 (< (f1_2 x15 x6) 12)) (?v_181 (< x15 6)) (?v_169 (= (f0_2 x5 x0) x15)) (?v_189 (< ?v_45 0)) (?v_32 (< x11 6)) (?v_119 (< x13 11)) (?v_180 (= (f0_2 x4 x18) (f0_2 x14 x2))) (?v_151 (< (f1_1 ?v_117) 15)) (?v_16 (< (f1_1 (f0_2 x4 x17)) 26)) (?v_116 (< ?v_55 1)) (?v_70 (< (f1_1 x18) 2))) (let ((?v_137 (< ?v_63 0)) (?v_40 (< ?v_13 25)) (?v_118 (< (f0_2 x16 x7) 27)) (?v_112 (< x12 11)) (?v_106 (< x6 3)) (?v_123 (< ?v_53 19)) (?v_98 (< (f0_1 x18) 14)) (?v_15 (< x12 8)) (?v_96 (< ?v_26 5)) (?v_185 (< ?v_75 24)) (?v_89 (= x4 x3)) (?v_132 (< ?v_56 20)) (?v_221 (< x8 27)) (?v_172 (< (f0_1 x7) 13)) (?v_62 (< x13 12)) (?v_102 (not P16)) (?v_82 (not P1)) (?v_17 (not P6)) (?v_31 (not ?v_16))) (let ((?v_108 (not ?v_62)) (?v_220 (not P13)) (?v_187 (not P15)) (?v_133 (not ?v_32)) (?v_125 (not P10)) (?v_170 (not P9)) (?v_100 (not ?v_169)) (?v_87 (not ?v_98)) (?v_157 (not ?v_84)) (?v_103 (not ?v_132)) (?v_71 (not ?v_89)) (?v_198 (not P3)) (?v_127 (not P11)) (?v_193 (not ?v_70)) (?v_104 (not ?v_15)) (?v_237 (not P0)) (?v_191 (not P14))) (let ((?v_251 (or ?v_237 ?v_191)) (?v_209 (not P12)) (?v_92 (not P18)) (?v_213 (not ?v_118)) (?v_128 (not P5)) (?v_136 (not P17)) (?v_122 (not ?v_40)) (?v_141 (not ?v_112)) (?v_216 (not ?v_151)) (?v_179 (not ?v_123)) (?v_165 (not ?v_116)) (?v_206 (not ?v_185)) (?v_186 (not ?v_142)) (?v_178 (not ?v_119)) (?v_168 (not ?v_180)) (?v_231 (not P19)) (?v_229 (not P7)) (?v_215 (not ?v_96)) (?v_194 (not P8)) (?v_182 (not P4)) (?v_199 (not ?v_106)) (?v_224 (not P2)) (?v_233 (not ?v_137)) (?v_228 (not ?v_221)) (?v_241 (not ?v_181)) (?v_232 (not ?v_172)) (?v_23 (+ (* 24 x5) (* 10 x2) (* 19 x8))) (?v_2 (f1_1 (+ (* 20 x9) (* 9 x5) (* 27 x15))))) (let ((?v_50 (< ?v_2 12)) (?v_30 (< ?v_23 26))) (let ((?v_174 (not ?v_30)) (?v_143 (not ?v_50)) (?v_188 (< ?v_23 19))) (let ((?v_248 (not ?v_188)) (?v_48 (- (- (* (- 15) x12) (* 12 x15)) (* 14 x14)))) (let ((?v_35 (f1_2 x7 ?v_48))) (let ((?v_6 (< ?v_35 (- 22))) (?v_93 (< (- (- (* (- 3) x6) (* 12 x12)) (* 12 x5)) 14)) (?v_0 (+ (* (- 9) x12) (* 14 x6) (* 16 x11)))) (let ((?v_4 (f0_2 ?v_0 ?v_23))) (let ((?v_14 (+ (* (- 12) ?v_4) (* 27 x7) (* 27 ?v_0)))) (let ((?v_245 (< ?v_14 11))) (let ((?v_59 (not ?v_245)) (?v_36 (- (- (* (- 2) x17) (* 10 x10)) (* 12 x19)))) (let ((?v_12 (< ?v_36 (- 18)))) (let ((?v_29 (not ?v_12)) (?v_1 (- (+ (* (- 17) x11) (* 4 x19)) (* 4 x7)))) (let ((?v_49 (- (+ (* (- 27) x14) ?v_61) (* 9 ?v_1)))) (let ((?v_3 (= ?v_95 ?v_49)) (?v_24 (- (+ (* (- 8) ?v_55) (* 5 ?v_1)) (* 15 x10)))) (let ((?v_39 (< ?v_24 29)) (?v_247 (< (f0_1 x19) (- 17)))) (let ((?v_21 (not ?v_247)) (?v_57 (< ?v_2 (- 21)))) (let ((?v_129 (not ?v_57)) (?v_46 (not ?v_3)) (?v_10 (< x18 (- 11))) (?v_7 (< ?v_13 (- 13))) (?v_8 (- (- (* (- 2) x14) (* 13 x12)) (* 4 x11)))) (let ((?v_5 (< ?v_8 (- 20)))) (let ((?v_222 (not ?v_5)) (?v_155 (< x12 (- 18)))) (let ((?v_83 (not ?v_155)) (?v_11 (= ?v_4 ?v_0)) (?v_43 (< (f0_2 x19 x10) (- 12)))) (let ((?v_60 (not ?v_43)) (?v_20 (not ?v_7)) (?v_211 (< (f1_1 x0) (- 1)))) (let ((?v_150 (not ?v_211)) (?v_18 (+ (- (* (- 20) x17) (* 13 x8)) (* 2 x3))) (?v_19 (- (- (* (- 8) x16) (* 22 x17)) (* 6 x6)))) (let ((?v_25 (f0_1 ?v_19))) (let ((?v_9 (= ?v_18 ?v_25))) (let ((?v_158 (not ?v_9)) (?v_28 (< ?v_8 (- 21))) (?v_68 (= (+ (* (- 3) x9) (* 14 x18) (* 26 x15)) ?v_56))) (let ((?v_65 (not ?v_68)) (?v_171 (not ?v_10)) (?v_235 (< ?v_14 (- 6)))) (let ((?v_51 (not ?v_235)) (?v_195 (< ?v_18 18))) (let ((?v_131 (not ?v_195)) (?v_22 (- (- (* (- 10) x0) (* 20 x3)) (* 11 x2)))) (let ((?v_34 (< ?v_22 28))) (let ((?v_94 (not ?v_34)) (?v_37 (< x3 (- 26)))) (let ((?v_147 (not ?v_37)) (?v_148 (< ?v_19 7)) (?v_110 (< ?v_22 (- 16))) (?v_41 (+ (- (* (- 3) x1) (* 17 ?v_45)) (* 27 ?v_2)))) (let ((?v_164 (< ?v_41 3))) (let ((?v_208 (not ?v_164)) (?v_42 (< ?v_24 16))) (let ((?v_175 (not ?v_42)) (?v_54 (< ?v_2 (- 18)))) (let ((?v_214 (not ?v_54)) (?v_27 (f1_2 ?v_25 ?v_26))) (let ((?v_44 (< ?v_27 13)) (?v_33 (< (f1_2 x4 x9) (- 27)))) (let ((?v_64 (not ?v_33)) (?v_124 (< ?v_27 (- 11)))) (let ((?v_166 (not ?v_124)) (?v_144 (f1_2 (+ (* 18 x10) (* 28 x1) (* 14 x9)) ?v_25))) (let ((?v_47 (= x13 ?v_144)) (?v_234 (not ?v_28)) (?v_205 (= ?v_117 ?v_8))) (let ((?v_115 (not ?v_205)) (?v_38 (< ?v_2 (- 25))) (?v_240 (= ?v_35 ?v_36)) (?v_167 (< x3 (- 18)))) (let ((?v_183 (not ?v_167)) (?v_227 (not ?v_38)) (?v_69 (not ?v_39)) (?v_58 (= ?v_19 x17)) (?v_105 (= ?v_41 ?v_2))) (let ((?v_210 (not ?v_105)) (?v_212 (not ?v_11)) (?v_52 (not ?v_44)) (?v_90 (< ?v_45 (- 1)))) (let ((?v_74 (not ?v_90)) (?v_192 (not ?v_47)) (?v_121 (= x7 ?v_48))) (let ((?v_66 (not ?v_121)) (?v_77 (< ?v_49 2))) (let ((?v_139 (not ?v_77)) (?v_161 (< ?v_53 (- 6)))) (let ((?v_85 (not ?v_161)) (?v_130 (< x4 (- 27))) (?v_97 (= ?v_25 ?v_2))) (let ((?v_225 (not ?v_97)) (?v_107 (< ?v_35 10))) (let ((?v_149 (not ?v_107)) (?v_184 (< ?v_25 (- 25)))) (let ((?v_177 (not ?v_184)) (?v_67 (not ?v_58)) (?v_201 (+ (- (* (- 20) x2) (* 13 x15)) (* 14 x17)))) (let ((?v_76 (= (f1_2 x11 x0) ?v_201))) (let ((?v_109 (not ?v_76)) (?v_80 (= (- (- (* (- 28) x5) (* 8 x18)) (* 23 x12)) (+ (- (* (- 17) x14) (* 17 x17)) ?v_61))) (?v_162 (< ?v_26 (- 8)))) (let ((?v_81 (not ?v_162)) (?v_88 (+ (* (- 14) x9) (* 16 x13) (* 17 x8)))) (let ((?v_203 (- (- (* (- 8) ?v_88) (* 12 (f1_1 ?v_63))) (* 21 x13)))) (let ((?v_72 (< ?v_203 2))) (let ((?v_163 (not ?v_72)) (?v_73 (< ?v_48 12))) (let ((?v_154 (not ?v_73)) (?v_101 (= ?v_2 ?v_48)) (?v_138 (< (f0_1 ?v_48) (- 14)))) (let ((?v_113 (not ?v_138)) (?v_78 (< ?v_75 (- 18)))) (let ((?v_250 (not ?v_78)) (?v_160 (< ?v_48 (- 11)))) (let ((?v_111 (not ?v_160)) (?v_217 (< ?v_25 (- 26)))) (let ((?v_135 (not ?v_217)) (?v_79 (< ?v_75 (- 3)))) (let ((?v_190 (not ?v_79)) (?v_153 (< ?v_23 (- 9))) (?v_86 (< ?v_48 (- 5)))) (let ((?v_91 (not ?v_86)) (?v_176 (not ?v_80)) (?v_120 (< (f0_2 ?v_45 ?v_13) (- 27))) (?v_99 (< ?v_88 9)) (?v_114 (< ?v_95 (- 17)))) (let ((?v_145 (not ?v_99)) (?v_152 (< ?v_2 (- 16)))) (let ((?v_140 (not ?v_152)) (?v_239 (not ?v_101)) (?v_126 (< x15 (- 9))) (?v_200 (not ?v_120))) (let ((?v_146 (not ?v_126)) (?v_196 (not ?v_110)) (?v_159 (< ?v_18 (- 16)))) (let ((?v_134 (not ?v_159)) (?v_197 (not ?v_93)) (?v_156 (< ?v_144 (- 14))) (?v_219 (not ?v_153))) (let ((?v_173 (not ?v_156)) (?v_204 (not ?v_114)) (?v_246 (or ?v_37 ?v_151)) (?v_230 (not ?v_148)) (?v_218 (< x0 (- 6))) (?v_207 (or ?v_142 ?v_54)) (?v_236 (= (- (- (* 2 ?v_201) (* 25 x15)) (* 15 ?v_202)) ?v_203)) (?v_226 (= ?v_25 ?v_201)) (?v_249 (< x14 (- 7))) (?v_223 (not ?v_130))) (let ((?v_242 (not ?v_218)) (?v_238 (not ?v_236)) (?v_244 (not ?v_240)) (?v_243 (not ?v_6))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or (or ?v_6 ?v_93) ?v_59) (or (or ?v_96 ?v_29) P12)) (or (or ?v_102 ?v_3) ?v_39)) (or (or ?v_15 ?v_21) ?v_50)) (or (or ?v_129 ?v_46) ?v_10)) (or (or ?v_137 ?v_123) ?v_7)) (or (or ?v_16 ?v_222) ?v_83)) (or (or ?v_11 ?v_60) ?v_5)) (or (or ?v_6 P6) ?v_20)) (or (or ?v_150 ?v_158) P6)) (or (or ?v_28 ?v_9) ?v_65)) (or (or ?v_171 ?v_82) ?v_11)) (or (or ?v_17 ?v_12) ?v_40)) (or (or ?v_6 ?v_51) ?v_15)) (or (or ?v_31 ?v_17) ?v_131)) (or (or P7 ?v_7) ?v_94)) (or (or ?v_147 ?v_148) ?v_20)) (or (or ?v_21 ?v_110) ?v_174)) (or (or ?v_208 ?v_175) ?v_108)) (or (or ?v_214 ?v_44) ?v_64)) (or (or ?v_220 ?v_166) ?v_7)) (or (or ?v_47 ?v_187) P17)) (or (or ?v_234 ?v_133) ?v_125)) (or (or ?v_115 ?v_29) ?v_30)) (or (or ?v_170 ?v_31) ?v_32)) (or (or ?v_33 ?v_38) ?v_34)) (or (or P18 ?v_240) ?v_183)) (or (or P13 ?v_37) ?v_227)) (or (or ?v_29 P18) P10)) (or (or ?v_69 ?v_58) P5)) (or (or ?v_40 ?v_210) ?v_42)) (or (or ?v_33 ?v_43) ?v_212)) (or (or ?v_52 ?v_74) ?v_46)) (or (or ?v_192 ?v_17) ?v_66)) (or (or ?v_139 ?v_100) ?v_50)) (or (or ?v_51 ?v_52) P13)) (or (or ?v_28 ?v_85) ?v_54)) (or (or ?v_130 ?v_87) ?v_5)) (or (or ?v_116 ?v_157) ?v_225)) (or (or ?v_149 ?v_103) P18)) (or (or ?v_57 ?v_177) ?v_16)) (or (or ?v_32 P18) ?v_67)) (or (or ?v_59 ?v_60) ?v_109)) (or (or ?v_71 ?v_57) ?v_80)) (or (or ?v_62 ?v_81) ?v_39)) (or (or ?v_163 ?v_154) ?v_64)) (or (or ?v_65 ?v_101) ?v_66)) (or (or ?v_43 ?v_70) P5)) (or (or ?v_112 ?v_198) ?v_127)) (or (or ?v_67 ?v_113) ?v_68)) (or (or ?v_250 ?v_69) ?v_193)) (or (or ?v_189 ?v_71) ?v_104)) (or (or ?v_40 ?v_72) ?v_73)) (or (or ?v_111 P1) ?v_33)) (or (or ?v_74 ?v_135) ?v_190)) (or (or ?v_76 ?v_153) ?v_77)) (or (or ?v_62 ?v_11) ?v_78)) (or ?v_251 P5)) (or (or P9 ?v_51) ?v_79)) (or (or ?v_209 ?v_91) ?v_176)) (or (or ?v_181 ?v_30) ?v_31)) (or (or ?v_20 ?v_221) ?v_74)) (or (or ?v_81 ?v_106) ?v_73)) (or (or ?v_82 P18) ?v_83)) (or (or ?v_84 ?v_85) ?v_86)) (or (or ?v_87 ?v_120) ?v_99)) (or (or P17 ?v_92) ?v_89)) (or (or ?v_90 ?v_91) ?v_92)) (or (or ?v_93 P9) ?v_94)) (or (or ?v_114 ?v_68) ?v_96)) (or (or ?v_89 ?v_97) ?v_98)) (or (or ?v_145 ?v_100) ?v_101)) (or (or ?v_97 ?v_102) ?v_15)) (or (or P6 ?v_103) ?v_94)) (or (or ?v_140 ?v_80) ?v_104)) (or (or ?v_213 ?v_17) ?v_105)) (or (or ?v_34 ?v_60) ?v_80)) (or (or ?v_86 ?v_73) ?v_128)) (or (or ?v_106 ?v_107) ?v_136)) (or (or ?v_72 ?v_108) ?v_122)) (or (or ?v_109 ?v_110) ?v_239)) (or (or ?v_100 ?v_98) ?v_5)) (or (or ?v_111 ?v_110) ?v_141)) (or (or ?v_113 ?v_71) ?v_143)) (or (or P16 P4) ?v_114)) (or (or ?v_21 ?v_62) ?v_115)) (or (or ?v_3 ?v_119) ?v_96)) (or (or ?v_116 ?v_216) ?v_118)) (or (or ?v_126 ?v_119) ?v_38)) (or (or ?v_200 ?v_121) ?v_122)) (or (or P16 ?v_62) P0)) (or (or ?v_15 ?v_119) ?v_179)) (or (or ?v_94 ?v_79) P3)) (or (or ?v_21 ?v_165) ?v_50)) (or (or ?v_124 ?v_125) ?v_146)) (or (or ?v_84 ?v_127) ?v_128)) (or (or ?v_196 ?v_93) ?v_51)) (or (or ?v_134 ?v_94) ?v_129)) (or (or ?v_50 ?v_70) P10)) (or (or ?v_197 ?v_142) ?v_130)) (or (or ?v_44 P15) ?v_206)) (or (or ?v_79 ?v_131) ?v_123)) (or (or ?v_59 ?v_11) ?v_132)) (or (or ?v_84 ?v_133) ?v_57)) (or (or ?v_57 ?v_72) ?v_134)) (or (or ?v_135 ?v_106) ?v_72)) (or (or P10 ?v_136) ?v_110)) (or (or ?v_137 ?v_138) ?v_139)) (or (or ?v_140 ?v_141) ?v_82)) (or (or ?v_186 ?v_143) ?v_156)) (or (or ?v_145 ?v_51) ?v_134)) (or (or ?v_16 ?v_20) ?v_115)) (or (or ?v_146 P8) ?v_147)) (or (or P18 ?v_21) ?v_148)) (or (or ?v_149 ?v_17) ?v_125)) (or (or ?v_28 ?v_150) ?v_151)) (or (or ?v_152 ?v_112) ?v_219)) (or (or ?v_127 ?v_154) ?v_70)) (or (or P14 ?v_76) ?v_81)) (or (or ?v_16 ?v_104) ?v_87)) (or (or ?v_32 ?v_146) P13)) (or (or ?v_155 ?v_173) ?v_157)) (or (or ?v_158 ?v_159) ?v_113)) (or (or ?v_3 ?v_160) ?v_178)) (or (or ?v_161 P4) P0)) (or (or ?v_168 ?v_99) ?v_204)) (or (or ?v_231 ?v_120) ?v_122)) (or (or ?v_162 ?v_163) ?v_134)) (or (or ?v_164 ?v_172) ?v_165)) (or (or ?v_166 ?v_30) ?v_10)) (or (or ?v_158 ?v_147) ?v_229)) (or (or ?v_248 ?v_60) ?v_16)) (or (or P7 ?v_124) ?v_167)) (or (or ?v_153 ?v_52) ?v_47)) (or ?v_246 ?v_215)) (or (or ?v_130 ?v_164) ?v_168)) (or (or ?v_28 ?v_169) ?v_70)) (or (or ?v_54 P3) ?v_170)) (or (or ?v_123 ?v_130) ?v_104)) (or (or ?v_21 ?v_6) ?v_171)) (or (or ?v_108 ?v_98) ?v_85)) (or (or ?v_143 ?v_172) ?v_40)) (or (or ?v_29 ?v_118) ?v_76)) (or (or ?v_230 ?v_32) ?v_163)) (or (or P12 ?v_92) ?v_134)) (or (or ?v_154 ?v_173) ?v_174)) (or (or ?v_57 P15) ?v_173)) (or (or P12 ?v_66) ?v_30)) (or (or ?v_143 ?v_150) ?v_112)) (or (or ?v_175 ?v_176) P16)) (or (or ?v_97 ?v_177) ?v_178)) (or (or ?v_54 ?v_50) ?v_194)) (or (or ?v_99 ?v_179) ?v_57)) (or (or ?v_154 ?v_10) P18)) (or (or ?v_126 ?v_180) ?v_129)) (or (or ?v_140 ?v_182) ?v_141)) (or (or ?v_110 ?v_181) ?v_182)) (or (or ?v_183 ?v_184) ?v_185)) (or (or ?v_79 ?v_186) P11)) (or (or ?v_131 ?v_187) ?v_12)) (or (or P10 ?v_3) P13)) (or (or ?v_188 ?v_96) ?v_143)) (or (or ?v_164 ?v_105) ?v_163)) (or (or ?v_128 ?v_130) ?v_167)) (or (or ?v_130 ?v_218) ?v_189)) (or (or ?v_139 ?v_155) ?v_140)) (or (or ?v_31 ?v_130) ?v_30)) (or (or ?v_86 ?v_177) ?v_164)) (or (or ?v_190 ?v_191) ?v_71)) (or ?v_207 ?v_120)) (or (or ?v_133 ?v_85) ?v_183)) (or (or ?v_21 ?v_173) ?v_119)) (or (or ?v_109 ?v_171) ?v_62)) (or (or ?v_192 P2) ?v_193)) (or (or ?v_150 ?v_89) ?v_194)) (or (or ?v_100 ?v_199) ?v_30)) (or (or ?v_166 ?v_195) ?v_54)) (or (or ?v_196 ?v_38) ?v_194)) (or (or ?v_197 ?v_198) ?v_17)) (or (or ?v_83 ?v_199) ?v_100)) (or (or ?v_127 ?v_127) ?v_150)) (or (or ?v_200 ?v_236) ?v_81)) (or (or ?v_87 ?v_161) ?v_150)) (or (or ?v_204 P13) ?v_187)) (or (or ?v_54 P8) ?v_3)) (or (or P11 ?v_6) ?v_205)) (or (or ?v_7 ?v_194) ?v_54)) (or (or ?v_70 ?v_154) ?v_206)) (or (or ?v_62 ?v_143) ?v_110)) (or ?v_207 ?v_64)) (or (or ?v_20 ?v_182) ?v_183)) (or (or ?v_77 ?v_127) ?v_113)) (or (or ?v_132 ?v_208) P10)) (or (or P6 ?v_84) P12)) (or (or ?v_39 ?v_153) ?v_165)) (or (or ?v_9 ?v_107) P15)) (or (or ?v_181 ?v_129) ?v_102)) (or (or ?v_99 ?v_7) ?v_87)) (or (or ?v_70 ?v_209) ?v_39)) (or (or ?v_37 ?v_11) ?v_175)) (or (or P8 ?v_167) ?v_125)) (or (or ?v_191 ?v_158) ?v_210)) (or (or ?v_226 ?v_114) ?v_162)) (or (or ?v_176 ?v_157) ?v_46)) (or (or ?v_193 ?v_150) ?v_206)) (or (or ?v_7 P9) ?v_191)) (or (or ?v_211 ?v_99) ?v_181)) (or (or ?v_212 ?v_149) ?v_116)) (or (or ?v_176 ?v_43) ?v_180)) (or (or ?v_197 ?v_112) ?v_200)) (or (or ?v_110 ?v_197) ?v_6)) (or (or ?v_191 ?v_213) ?v_108)) (or (or ?v_31 ?v_181) ?v_97)) (or (or ?v_172 P7) ?v_12)) (or (or ?v_136 ?v_120) ?v_21)) (or (or ?v_64 ?v_109) ?v_67)) (or (or ?v_114 ?v_127) ?v_101)) (or (or ?v_138 ?v_107) ?v_135)) (or (or ?v_158 ?v_118) ?v_39)) (or (or ?v_214 ?v_32) ?v_62)) (or (or ?v_140 P16) ?v_68)) (or (or ?v_153 ?v_140) ?v_89)) (or (or ?v_129 ?v_113) ?v_109)) (or (or ?v_249 ?v_10) ?v_112)) (or (or ?v_215 ?v_42) P18)) (or (or ?v_81 ?v_15) ?v_6)) (or (or ?v_81 ?v_127) ?v_65)) (or (or ?v_223 ?v_173) ?v_224)) (or (or ?v_104 ?v_77) ?v_216)) (or (or ?v_66 ?v_96) ?v_217)) (or (or ?v_111 ?v_29) ?v_17)) (or (or ?v_15 ?v_154) P13)) (or (or ?v_42 ?v_120) ?v_233)) (or (or ?v_40 ?v_20) ?v_105)) (or (or ?v_89 ?v_161) ?v_242)) (or (or ?v_17 ?v_219) ?v_220)) (or (or ?v_15 ?v_159) ?v_67)) (or (or ?v_159 ?v_176) ?v_112)) (or (or ?v_90 ?v_119) P18)) (or (or ?v_165 ?v_155) ?v_160)) (or (or ?v_90 ?v_72) ?v_151)) (or (or ?v_129 ?v_107) ?v_148)) (or (or ?v_212 ?v_67) ?v_138)) (or (or ?v_228 ?v_131) ?v_81)) (or (or ?v_89 ?v_133) ?v_122)) (or (or ?v_206 ?v_166) ?v_183)) (or (or ?v_77 ?v_196) ?v_39)) (or (or ?v_37 ?v_83) ?v_222)) (or (or ?v_44 ?v_129) ?v_216)) (or (or ?v_156 ?v_16) ?v_176)) (or (or P9 ?v_5) ?v_51)) (or (or ?v_140 P8) ?v_181)) (or (or P19 ?v_196) ?v_191)) (or (or ?v_154 ?v_124) ?v_102)) (or (or ?v_174 ?v_32) P13)) (or (or ?v_73 ?v_15) ?v_62)) (or (or ?v_135 ?v_39) ?v_209)) (or (or ?v_155 ?v_148) ?v_140)) (or (or ?v_64 P5) ?v_12)) (or (or ?v_47 ?v_241) ?v_58)) (or (or ?v_204 ?v_64) ?v_171)) (or (or ?v_223 ?v_224) ?v_180)) (or (or ?v_136 ?v_219) ?v_148)) (or (or ?v_127 ?v_90) ?v_223)) (or (or ?v_85 ?v_225) ?v_84)) (or (or ?v_5 ?v_129) ?v_100)) (or (or ?v_89 ?v_5) ?v_185)) (or (or P19 ?v_85) ?v_79)) (or (or ?v_220 ?v_62) ?v_100)) (or (or ?v_5 ?v_107) ?v_226)) (or (or ?v_153 ?v_10) ?v_174)) (or (or ?v_214 ?v_76) ?v_115)) (or (or ?v_68 ?v_72) ?v_94)) (or (or ?v_227 ?v_223) ?v_228)) (or (or ?v_229 ?v_32) ?v_189)) (or (or ?v_135 ?v_90) ?v_65)) (or (or ?v_64 ?v_97) ?v_34)) (or (or ?v_50 ?v_159) ?v_230)) (or (or ?v_169 ?v_52) ?v_143)) (or (or ?v_118 ?v_231) ?v_232)) (or (or ?v_125 ?v_121) ?v_171)) (or (or ?v_128 ?v_39) ?v_132)) (or (or ?v_191 ?v_227) ?v_176)) (or (or ?v_79 ?v_110) ?v_70)) (or (or ?v_193 ?v_128) ?v_67)) (or (or ?v_147 ?v_3) ?v_225)) (or (or ?v_217 ?v_30) ?v_120)) (or (or ?v_116 ?v_179) ?v_148)) (or (or ?v_232 ?v_223) ?v_92)) (or (or ?v_123 ?v_177) ?v_183)) (or (or ?v_233 ?v_32) ?v_7)) (or (or ?v_234 ?v_77) ?v_85)) (or (or ?v_58 ?v_231) ?v_150)) (or (or ?v_105 P7) P4)) (or (or ?v_39 ?v_229) ?v_198)) (or (or ?v_40 ?v_128) ?v_200)) (or (or ?v_204 ?v_235) ?v_236)) (or (or ?v_84 ?v_11) ?v_213)) (or (or P2 ?v_54) ?v_238)) (or (or ?v_59 ?v_173) ?v_193)) (or (or ?v_140 ?v_145) ?v_113)) (or (or ?v_110 ?v_194) P6)) (or (or ?v_100 ?v_232) ?v_217)) (or (or ?v_37 ?v_124) P5)) (or (or ?v_228 ?v_145) ?v_7)) (or (or ?v_114 ?v_65) ?v_157)) (or (or P5 ?v_15) ?v_152)) (or (or ?v_170 ?v_96) ?v_123)) (or (or ?v_112 ?v_6) ?v_155)) (or (or ?v_237 ?v_46) ?v_217)) (or (or ?v_225 ?v_198) ?v_132)) (or (or ?v_10 P18) ?v_174)) (or (or ?v_121 ?v_108) ?v_238)) (or (or ?v_180 ?v_212) ?v_126)) (or (or ?v_226 ?v_115) ?v_190)) (or (or ?v_92 ?v_113) ?v_146)) (or (or ?v_153 ?v_92) ?v_166)) (or (or ?v_168 ?v_217) ?v_140)) (or (or ?v_107 ?v_188) ?v_44)) (or (or ?v_182 ?v_103) ?v_112)) (or (or P9 ?v_172) ?v_81)) (or (or ?v_237 P14) ?v_146)) (or (or ?v_194 ?v_121) ?v_81)) (or (or P19 ?v_12) ?v_226)) (or (or ?v_133 ?v_112) ?v_236)) (or (or ?v_154 ?v_163) P1)) (or (or ?v_30 ?v_58) ?v_79)) (or (or ?v_225 P18) ?v_194)) (or (or ?v_221 ?v_148) ?v_40)) (or (or ?v_47 ?v_174) ?v_71)) (or (or ?v_104 ?v_157) ?v_52)) (or (or ?v_179 ?v_178) ?v_239)) (or (or ?v_43 ?v_150) ?v_232)) (or (or ?v_221 ?v_225) ?v_78)) (or (or ?v_93 ?v_31) ?v_227)) (or (or ?v_140 ?v_222) ?v_205)) (or (or P11 ?v_221) ?v_163)) (or (or P7 ?v_31) ?v_102)) (or (or ?v_185 P9) ?v_188)) (or (or ?v_86 ?v_197) ?v_11)) (or (or P12 ?v_147) P2)) (or (or ?v_157 ?v_83) ?v_167)) (or (or ?v_38 ?v_137) ?v_142)) (or (or ?v_143 ?v_70) ?v_89)) (or (or ?v_7 ?v_182) ?v_38)) (or (or ?v_135 P12) ?v_72)) (or (or P1 ?v_244) ?v_226)) (or (or ?v_235 P10) ?v_129)) (or (or ?v_17 ?v_118) ?v_161)) (or (or ?v_243 ?v_219) ?v_20)) (or (or ?v_62 P11) ?v_68)) (or (or ?v_210 ?v_215) (not ?v_226))) (or (or ?v_54 ?v_190) ?v_6)) (or (or ?v_227 ?v_220) ?v_80)) (or (or ?v_214 ?v_42) ?v_240)) (or (or ?v_241 ?v_238) ?v_146)) (or (or ?v_91 ?v_216) ?v_194)) (or (or ?v_69 ?v_209) ?v_90)) (or (or ?v_124 ?v_50) ?v_34)) (or (or ?v_213 ?v_142) ?v_173)) (or (or ?v_59 ?v_84) ?v_242)) (or (or ?v_139 ?v_64) ?v_83)) (or (or ?v_172 ?v_198) ?v_243)) (or (or ?v_59 ?v_47) ?v_244)) (or (or ?v_134 ?v_181) P6)) (or (or P5 ?v_72) P10)) (or (or ?v_208 ?v_122) ?v_237)) (or (or ?v_218 P4) ?v_154)) (or (or ?v_178 ?v_17) ?v_114)) (or (or ?v_240 ?v_108) ?v_60)) (or (or ?v_211 ?v_42) P10)) (or (or ?v_174 ?v_143) ?v_178)) (or (or ?v_46 P10) ?v_74)) (or (or ?v_149 ?v_29) ?v_206)) (or (or ?v_7 ?v_93) ?v_242)) (or (or ?v_52 P4) ?v_232)) (or (or ?v_172 ?v_218) ?v_195)) (or (or ?v_15 ?v_101) ?v_243)) (or (or ?v_59 ?v_126) ?v_175)) (or (or ?v_158 ?v_107) P14)) (or (or P4 ?v_215) P2)) (or (or ?v_188 ?v_29) ?v_54)) (or (or ?v_199 ?v_178) ?v_111)) (or (or ?v_119 ?v_114) ?v_190)) (or (or ?v_102 ?v_133) ?v_210)) (or (or ?v_28 ?v_69) ?v_149)) (or (or ?v_33 ?v_92) ?v_146)) (or (or ?v_139 ?v_105) ?v_15)) (or (or P1 ?v_221) ?v_135)) (or (or ?v_163 ?v_189) ?v_69)) (or (or ?v_139 ?v_245) ?v_191)) (or (or ?v_194 ?v_227) ?v_220)) (or (or ?v_239 P1) ?v_210)) (or (or ?v_211 ?v_204) ?v_31)) (or (or ?v_28 ?v_175) ?v_30)) (or (or ?v_224 ?v_79) ?v_133)) (or (or ?v_72 ?v_133) ?v_236)) (or (or ?v_47 ?v_91) ?v_180)) (or (or ?v_76 ?v_162) ?v_179)) (or (or ?v_191 ?v_94) ?v_17)) (or (or ?v_147 ?v_176) ?v_112)) (or ?v_246 ?v_3)) (or (or ?v_136 ?v_247) ?v_12)) (or (or ?v_138 ?v_74) ?v_189)) (or (or ?v_169 ?v_238) ?v_34)) (or (or P3 ?v_217) ?v_208)) (or (or ?v_21 ?v_50) ?v_217)) (or (or ?v_162 ?v_177) ?v_218)) (or (or ?v_52 ?v_80) ?v_195)) (or (or ?v_67 ?v_101) ?v_238)) (or (or ?v_213 ?v_199) ?v_236)) (or (or ?v_148 ?v_153) ?v_17)) (or (or ?v_87 ?v_113) P9)) (or (or ?v_196 P4) ?v_83)) (or (or ?v_99 ?v_248) ?v_214)) (or (or ?v_103 ?v_174) ?v_91)) (or (or P5 ?v_249) ?v_204)) (or (or ?v_105 ?v_238) ?v_60)) (or (or ?v_214 ?v_130) ?v_136)) (or (or ?v_164 ?v_230) ?v_174)) (or (or ?v_156 ?v_93) ?v_64)) (or (or ?v_183 ?v_126) ?v_131)) (or (or ?v_110 ?v_223) ?v_155)) (or (or ?v_77 ?v_176) ?v_96)) (or (or ?v_39 ?v_170) P15)) (or (or ?v_126 ?v_140) ?v_132)) (or (or ?v_100 ?v_154) P8)) (or (or ?v_227 ?v_212) ?v_145)) (or (or ?v_171 ?v_233) ?v_182)) (or (or ?v_87 ?v_116) ?v_5)) (or (or ?v_240 ?v_234) ?v_178)) (or (or ?v_86 ?v_42) ?v_151)) (or (or P18 ?v_162) ?v_17)) (or (or ?v_164 ?v_193) ?v_50)) (or (or ?v_247 ?v_17) ?v_196)) (or (or ?v_211 ?v_116) ?v_111)) (or (or ?v_145 ?v_59) ?v_94)) (or (or ?v_157 ?v_240) P11)) (or (or ?v_221 P14) ?v_9)) (or (or ?v_213 ?v_145) ?v_208)) (or (or ?v_225 ?v_10) ?v_164)) (or (or ?v_40 ?v_119) ?v_66)) (or (or ?v_80 P5) ?v_113)) (or (or ?v_33 ?v_195) ?v_239)) (or (or ?v_106 ?v_87) ?v_33)) (or (or ?v_233 ?v_135) ?v_128)) (or (or P0 ?v_142) ?v_68)) (or (or ?v_92 ?v_72) ?v_167)) (or (or ?v_224 ?v_130) ?v_167)) (or (or ?v_20 ?v_68) P7)) (or (or ?v_165 ?v_20) ?v_168)) (or (or ?v_196 ?v_200) ?v_165)) (or (or ?v_217 ?v_100) ?v_189)) (or (or ?v_10 ?v_102) P13)) (or (or ?v_47 ?v_182) ?v_222)) (or (or P18 ?v_205) ?v_125)) (or (or ?v_212 ?v_205) ?v_110)) (or (or ?v_90 P14) ?v_80)) (or (or ?v_113 ?v_158) ?v_151)) (or (or (not ?v_249) ?v_20) ?v_73)) (or (or ?v_235 ?v_34) ?v_161)) (or (or ?v_69 ?v_16) ?v_78)) (or (or ?v_15 P6) ?v_46)) (or (or ?v_87 ?v_234) ?v_232)) (or (or ?v_31 ?v_216) ?v_93)) (or (or ?v_118 P3) ?v_188)) (or (or ?v_5 ?v_54) ?v_168)) (or (or ?v_30 ?v_195) ?v_240)) (or (or ?v_3 ?v_67) ?v_220)) (or (or ?v_145 ?v_189) ?v_140)) (or (or ?v_228 ?v_105) ?v_76)) (or (or ?v_141 ?v_69) ?v_149)) (or (or ?v_197 ?v_93) ?v_169)) (or (or ?v_173 P9) ?v_135)) (or (or ?v_186 ?v_86) ?v_180)) (or (or ?v_43 ?v_110) ?v_126)) (or (or ?v_172 ?v_158) ?v_33)) (or (or ?v_238 ?v_32) ?v_247)) (or (or ?v_185 ?v_93) ?v_208)) (or (or P4 ?v_54) ?v_85)) (or (or ?v_28 ?v_57) ?v_210)) (or (or ?v_245 ?v_29) ?v_90)) (or (or ?v_37 ?v_106) ?v_65)) (or (or ?v_247 ?v_186) ?v_204)) (or (or ?v_94 ?v_167) ?v_164)) (or (or ?v_120 ?v_197) ?v_21)) (or (or ?v_81 ?v_167) ?v_219)) (or (or ?v_134 ?v_230) ?v_157)) (or (or P11 ?v_151) ?v_171)) (or (or ?v_90 ?v_194) ?v_137)) (or (or ?v_114 ?v_250) ?v_170)) (or (or ?v_211 ?v_249) ?v_60)) (or (or ?v_21 ?v_171) ?v_213)) (or (or ?v_184 ?v_43) P8)) (or (or ?v_42 ?v_241) ?v_64)) (or (or ?v_87 ?v_153) ?v_60)) (or (or ?v_173 ?v_241) P0)) (or (or ?v_78 ?v_86) P18)) (or (or ?v_142 ?v_191) ?v_116)) (or ?v_251 ?v_214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
