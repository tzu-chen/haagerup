module

public import HaagerupIzumi.C8.Lattice.S2CloseMem
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# The 600 operator relations of the minimal-generation record, collected

`s2op_mem_k`: `op_o r_k ∈ S₂` for the five operators `E_L(0), F_L(0), E_R(0), F_R(0), u_(1)`
(`o = 0, …, 4`), from the relation memberships `s2src_mem_i` of `S2CloseMem.lean`;
`s2op_mem`: the same for every vector of `s2basis`.  Used in `S2Closure.lean`.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

theorem s2op_mem_0 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_0) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_44, s2src_mem_45, s2src_mem_46, s2src_mem_47, s2src_mem_48]

theorem s2op_mem_1 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_1) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_49, s2src_mem_50, s2src_mem_51, s2src_mem_52, s2src_mem_53]

theorem s2op_mem_2 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_2) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_54, s2src_mem_55, s2src_mem_56, s2src_mem_57, s2src_mem_58]

theorem s2op_mem_3 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_3) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_59, s2src_mem_60, s2src_mem_61, s2src_mem_62, s2src_mem_63]

theorem s2op_mem_4 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_4) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_64, s2src_mem_65, s2src_mem_66, s2src_mem_67, s2src_mem_68]

theorem s2op_mem_5 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_5) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_69, s2src_mem_70, s2src_mem_71, s2src_mem_72, s2src_mem_73]

theorem s2op_mem_6 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_6) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_74, s2src_mem_75, s2src_mem_76, s2src_mem_77, s2src_mem_78]

theorem s2op_mem_7 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_7) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_79, s2src_mem_80, s2src_mem_81, s2src_mem_82, s2src_mem_83]

theorem s2op_mem_8 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_8) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_84, s2src_mem_85, s2src_mem_86, s2src_mem_87, s2src_mem_88]

theorem s2op_mem_9 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_9) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_89, s2src_mem_90, s2src_mem_91, s2src_mem_92, s2src_mem_93]

theorem s2op_mem_10 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_10) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_94, s2src_mem_95, s2src_mem_96, s2src_mem_97, s2src_mem_98]

theorem s2op_mem_11 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_11) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_99, s2src_mem_100, s2src_mem_101, s2src_mem_102, s2src_mem_103]

theorem s2op_mem_12 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_12) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_104, s2src_mem_105, s2src_mem_106, s2src_mem_107, s2src_mem_108]

theorem s2op_mem_13 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_13) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_109, s2src_mem_110, s2src_mem_111, s2src_mem_112, s2src_mem_113]

theorem s2op_mem_14 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_14) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_114, s2src_mem_115, s2src_mem_116, s2src_mem_117, s2src_mem_118]

theorem s2op_mem_15 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_15) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_119, s2src_mem_120, s2src_mem_121, s2src_mem_122, s2src_mem_123]

theorem s2op_mem_16 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_16) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_124, s2src_mem_125, s2src_mem_126, s2src_mem_127, s2src_mem_128]

theorem s2op_mem_17 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_17) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_129, s2src_mem_130, s2src_mem_131, s2src_mem_132, s2src_mem_133]

theorem s2op_mem_18 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_18) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_134, s2src_mem_135, s2src_mem_136, s2src_mem_137, s2src_mem_138]

theorem s2op_mem_19 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_19) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_139, s2src_mem_140, s2src_mem_141, s2src_mem_142, s2src_mem_143]

theorem s2op_mem_20 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_20) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_144, s2src_mem_145, s2src_mem_146, s2src_mem_147, s2src_mem_148]

theorem s2op_mem_21 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_21) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_149, s2src_mem_150, s2src_mem_151, s2src_mem_152, s2src_mem_153]

theorem s2op_mem_22 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_22) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_154, s2src_mem_155, s2src_mem_156, s2src_mem_157, s2src_mem_158]

theorem s2op_mem_23 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_23) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_159, s2src_mem_160, s2src_mem_161, s2src_mem_162, s2src_mem_163]

theorem s2op_mem_24 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_24) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_164, s2src_mem_165, s2src_mem_166, s2src_mem_167, s2src_mem_168]

theorem s2op_mem_25 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_25) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_169, s2src_mem_170, s2src_mem_171, s2src_mem_172, s2src_mem_173]

theorem s2op_mem_26 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_26) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_174, s2src_mem_175, s2src_mem_176, s2src_mem_177, s2src_mem_178]

theorem s2op_mem_27 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_27) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_179, s2src_mem_180, s2src_mem_181, s2src_mem_182, s2src_mem_183]

theorem s2op_mem_28 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_28) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_184, s2src_mem_185, s2src_mem_186, s2src_mem_187, s2src_mem_188]

theorem s2op_mem_29 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_29) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_189, s2src_mem_190, s2src_mem_191, s2src_mem_192, s2src_mem_193]

theorem s2op_mem_30 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_30) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_194, s2src_mem_195, s2src_mem_196, s2src_mem_197, s2src_mem_198]

theorem s2op_mem_31 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_31) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_199, s2src_mem_200, s2src_mem_201, s2src_mem_202, s2src_mem_203]

theorem s2op_mem_32 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_32) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_204, s2src_mem_205, s2src_mem_206, s2src_mem_207, s2src_mem_208]

theorem s2op_mem_33 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_33) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_209, s2src_mem_210, s2src_mem_211, s2src_mem_212, s2src_mem_213]

theorem s2op_mem_34 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_34) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_214, s2src_mem_215, s2src_mem_216, s2src_mem_217, s2src_mem_218]

theorem s2op_mem_35 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_35) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_219, s2src_mem_220, s2src_mem_221, s2src_mem_222, s2src_mem_223]

theorem s2op_mem_36 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_36) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_224, s2src_mem_225, s2src_mem_226, s2src_mem_227, s2src_mem_228]

theorem s2op_mem_37 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_37) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_229, s2src_mem_230, s2src_mem_231, s2src_mem_232, s2src_mem_233]

theorem s2op_mem_38 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_38) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_234, s2src_mem_235, s2src_mem_236, s2src_mem_237, s2src_mem_238]

theorem s2op_mem_39 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_39) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_239, s2src_mem_240, s2src_mem_241, s2src_mem_242, s2src_mem_243]

theorem s2op_mem_40 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_40) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_244, s2src_mem_245, s2src_mem_246, s2src_mem_247, s2src_mem_248]

theorem s2op_mem_41 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_41) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_249, s2src_mem_250, s2src_mem_251, s2src_mem_252, s2src_mem_253]

theorem s2op_mem_42 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_42) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_254, s2src_mem_255, s2src_mem_256, s2src_mem_257, s2src_mem_258]

theorem s2op_mem_43 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_43) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_259, s2src_mem_260, s2src_mem_261, s2src_mem_262, s2src_mem_263]

theorem s2op_mem_44 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_44) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_264, s2src_mem_265, s2src_mem_266, s2src_mem_267, s2src_mem_268]

theorem s2op_mem_45 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_45) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_269, s2src_mem_270, s2src_mem_271, s2src_mem_272, s2src_mem_273]

theorem s2op_mem_46 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_46) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_274, s2src_mem_275, s2src_mem_276, s2src_mem_277, s2src_mem_278]

theorem s2op_mem_47 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_47) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_279, s2src_mem_280, s2src_mem_281, s2src_mem_282, s2src_mem_283]

theorem s2op_mem_48 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_48) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_284, s2src_mem_285, s2src_mem_286, s2src_mem_287, s2src_mem_288]

theorem s2op_mem_49 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_49) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_289, s2src_mem_290, s2src_mem_291, s2src_mem_292, s2src_mem_293]

theorem s2op_mem_50 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_50) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_294, s2src_mem_295, s2src_mem_296, s2src_mem_297, s2src_mem_298]

theorem s2op_mem_51 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_51) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_299, s2src_mem_300, s2src_mem_301, s2src_mem_302, s2src_mem_303]

theorem s2op_mem_52 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_52) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_304, s2src_mem_305, s2src_mem_306, s2src_mem_307, s2src_mem_308]

theorem s2op_mem_53 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_53) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_309, s2src_mem_310, s2src_mem_311, s2src_mem_312, s2src_mem_313]

theorem s2op_mem_54 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_54) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_314, s2src_mem_315, s2src_mem_316, s2src_mem_317, s2src_mem_318]

theorem s2op_mem_55 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_55) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_319, s2src_mem_320, s2src_mem_321, s2src_mem_322, s2src_mem_323]

theorem s2op_mem_56 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_56) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_324, s2src_mem_325, s2src_mem_326, s2src_mem_327, s2src_mem_328]

theorem s2op_mem_57 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_57) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_329, s2src_mem_330, s2src_mem_331, s2src_mem_332, s2src_mem_333]

theorem s2op_mem_58 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_58) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_334, s2src_mem_335, s2src_mem_336, s2src_mem_337, s2src_mem_338]

theorem s2op_mem_59 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_59) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_339, s2src_mem_340, s2src_mem_341, s2src_mem_342, s2src_mem_343]

theorem s2op_mem_60 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_60) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_344, s2src_mem_345, s2src_mem_346, s2src_mem_347, s2src_mem_348]

theorem s2op_mem_61 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_61) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_349, s2src_mem_350, s2src_mem_351, s2src_mem_352, s2src_mem_353]

theorem s2op_mem_62 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_62) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_354, s2src_mem_355, s2src_mem_356, s2src_mem_357, s2src_mem_358]

theorem s2op_mem_63 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_63) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_359, s2src_mem_360, s2src_mem_361, s2src_mem_362, s2src_mem_363]

theorem s2op_mem_64 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_64) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_364, s2src_mem_365, s2src_mem_366, s2src_mem_367, s2src_mem_368]

theorem s2op_mem_65 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_65) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_369, s2src_mem_370, s2src_mem_371, s2src_mem_372, s2src_mem_373]

theorem s2op_mem_66 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_66) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_374, s2src_mem_375, s2src_mem_376, s2src_mem_377, s2src_mem_378]

theorem s2op_mem_67 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_67) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_379, s2src_mem_380, s2src_mem_381, s2src_mem_382, s2src_mem_383]

theorem s2op_mem_68 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_68) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_384, s2src_mem_385, s2src_mem_386, s2src_mem_387, s2src_mem_388]

theorem s2op_mem_69 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_69) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_389, s2src_mem_390, s2src_mem_391, s2src_mem_392, s2src_mem_393]

theorem s2op_mem_70 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_70) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_394, s2src_mem_395, s2src_mem_396, s2src_mem_397, s2src_mem_398]

theorem s2op_mem_71 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_71) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_399, s2src_mem_400, s2src_mem_401, s2src_mem_402, s2src_mem_403]

theorem s2op_mem_72 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_72) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_404, s2src_mem_405, s2src_mem_406, s2src_mem_407, s2src_mem_408]

theorem s2op_mem_73 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_73) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_409, s2src_mem_410, s2src_mem_411, s2src_mem_412, s2src_mem_413]

theorem s2op_mem_74 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_74) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_414, s2src_mem_415, s2src_mem_416, s2src_mem_417, s2src_mem_418]

theorem s2op_mem_75 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_75) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_419, s2src_mem_420, s2src_mem_421, s2src_mem_422, s2src_mem_423]

theorem s2op_mem_76 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_76) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_424, s2src_mem_425, s2src_mem_426, s2src_mem_427, s2src_mem_428]

theorem s2op_mem_77 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_77) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_429, s2src_mem_430, s2src_mem_431, s2src_mem_432, s2src_mem_433]

theorem s2op_mem_78 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_78) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_434, s2src_mem_435, s2src_mem_436, s2src_mem_437, s2src_mem_438]

theorem s2op_mem_79 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_79) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_439, s2src_mem_440, s2src_mem_441, s2src_mem_442, s2src_mem_443]

theorem s2op_mem_80 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_80) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_444, s2src_mem_445, s2src_mem_446, s2src_mem_447, s2src_mem_448]

theorem s2op_mem_81 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_81) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_449, s2src_mem_450, s2src_mem_451, s2src_mem_452, s2src_mem_453]

theorem s2op_mem_82 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_82) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_454, s2src_mem_455, s2src_mem_456, s2src_mem_457, s2src_mem_458]

theorem s2op_mem_83 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_83) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_459, s2src_mem_460, s2src_mem_461, s2src_mem_462, s2src_mem_463]

theorem s2op_mem_84 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_84) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_464, s2src_mem_465, s2src_mem_466, s2src_mem_467, s2src_mem_468]

theorem s2op_mem_85 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_85) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_469, s2src_mem_470, s2src_mem_471, s2src_mem_472, s2src_mem_473]

theorem s2op_mem_86 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_86) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_474, s2src_mem_475, s2src_mem_476, s2src_mem_477, s2src_mem_478]

theorem s2op_mem_87 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_87) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_479, s2src_mem_480, s2src_mem_481, s2src_mem_482, s2src_mem_483]

theorem s2op_mem_88 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_88) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_484, s2src_mem_485, s2src_mem_486, s2src_mem_487, s2src_mem_488]

theorem s2op_mem_89 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_89) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_489, s2src_mem_490, s2src_mem_491, s2src_mem_492, s2src_mem_493]

theorem s2op_mem_90 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_90) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_494, s2src_mem_495, s2src_mem_496, s2src_mem_497, s2src_mem_498]

theorem s2op_mem_91 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_91) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_499, s2src_mem_500, s2src_mem_501, s2src_mem_502, s2src_mem_503]

theorem s2op_mem_92 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_92) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_504, s2src_mem_505, s2src_mem_506, s2src_mem_507, s2src_mem_508]

theorem s2op_mem_93 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_93) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_509, s2src_mem_510, s2src_mem_511, s2src_mem_512, s2src_mem_513]

theorem s2op_mem_94 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_94) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_514, s2src_mem_515, s2src_mem_516, s2src_mem_517, s2src_mem_518]

theorem s2op_mem_95 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_95) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_519, s2src_mem_520, s2src_mem_521, s2src_mem_522, s2src_mem_523]

theorem s2op_mem_96 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_96) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_524, s2src_mem_525, s2src_mem_526, s2src_mem_527, s2src_mem_528]

theorem s2op_mem_97 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_97) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_529, s2src_mem_530, s2src_mem_531, s2src_mem_532, s2src_mem_533]

theorem s2op_mem_98 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_98) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_534, s2src_mem_535, s2src_mem_536, s2src_mem_537, s2src_mem_538]

theorem s2op_mem_99 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_99) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_539, s2src_mem_540, s2src_mem_541, s2src_mem_542, s2src_mem_543]

theorem s2op_mem_100 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_100) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_544, s2src_mem_545, s2src_mem_546, s2src_mem_547, s2src_mem_548]

theorem s2op_mem_101 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_101) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_549, s2src_mem_550, s2src_mem_551, s2src_mem_552, s2src_mem_553]

theorem s2op_mem_102 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_102) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_554, s2src_mem_555, s2src_mem_556, s2src_mem_557, s2src_mem_558]

theorem s2op_mem_103 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_103) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_559, s2src_mem_560, s2src_mem_561, s2src_mem_562, s2src_mem_563]

theorem s2op_mem_104 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_104) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_564, s2src_mem_565, s2src_mem_566, s2src_mem_567, s2src_mem_568]

theorem s2op_mem_105 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_105) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_569, s2src_mem_570, s2src_mem_571, s2src_mem_572, s2src_mem_573]

theorem s2op_mem_106 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_106) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_574, s2src_mem_575, s2src_mem_576, s2src_mem_577, s2src_mem_578]

theorem s2op_mem_107 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_107) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_579, s2src_mem_580, s2src_mem_581, s2src_mem_582, s2src_mem_583]

theorem s2op_mem_108 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_108) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_584, s2src_mem_585, s2src_mem_586, s2src_mem_587, s2src_mem_588]

theorem s2op_mem_109 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_109) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_589, s2src_mem_590, s2src_mem_591, s2src_mem_592, s2src_mem_593]

theorem s2op_mem_110 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_110) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_594, s2src_mem_595, s2src_mem_596, s2src_mem_597, s2src_mem_598]

theorem s2op_mem_111 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_111) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_599, s2src_mem_600, s2src_mem_601, s2src_mem_602, s2src_mem_603]

theorem s2op_mem_112 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_112) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_604, s2src_mem_605, s2src_mem_606, s2src_mem_607, s2src_mem_608]

theorem s2op_mem_113 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_113) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_609, s2src_mem_610, s2src_mem_611, s2src_mem_612, s2src_mem_613]

theorem s2op_mem_114 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_114) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_614, s2src_mem_615, s2src_mem_616, s2src_mem_617, s2src_mem_618]

theorem s2op_mem_115 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_115) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_619, s2src_mem_620, s2src_mem_621, s2src_mem_622, s2src_mem_623]

theorem s2op_mem_116 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_116) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_624, s2src_mem_625, s2src_mem_626, s2src_mem_627, s2src_mem_628]

theorem s2op_mem_117 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_117) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_629, s2src_mem_630, s2src_mem_631, s2src_mem_632, s2src_mem_633]

theorem s2op_mem_118 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_118) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_634, s2src_mem_635, s2src_mem_636, s2src_mem_637, s2src_mem_638]

theorem s2op_mem_119 : ∀ o : ℕ, o ≤ 4 → toV4 (Vec4.mode (s2op o) (s2opIdx o) s2r_119) ∈ S2span := by
  intro o ho
  interval_cases o
  exacts [s2src_mem_639, s2src_mem_640, s2src_mem_641, s2src_mem_642, s2src_mem_643]
/-- The 600 operator relations: `op_o r_k ∈ S₂`. -/
theorem s2op_mem : ∀ x ∈ s2basis, ∀ o : ℕ, o ≤ 4 →
    toV4 (Vec4.mode (s2op o) (s2opIdx o) x) ∈ S2span := by
  intro x hx
  simp only [s2basis, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [s2op_mem_0, s2op_mem_1, s2op_mem_2, s2op_mem_3, s2op_mem_4, s2op_mem_5, s2op_mem_6, s2op_mem_7, s2op_mem_8, s2op_mem_9, s2op_mem_10, s2op_mem_11, s2op_mem_12, s2op_mem_13, s2op_mem_14, s2op_mem_15, s2op_mem_16, s2op_mem_17, s2op_mem_18, s2op_mem_19, s2op_mem_20, s2op_mem_21, s2op_mem_22, s2op_mem_23, s2op_mem_24, s2op_mem_25, s2op_mem_26, s2op_mem_27, s2op_mem_28, s2op_mem_29, s2op_mem_30, s2op_mem_31, s2op_mem_32, s2op_mem_33, s2op_mem_34, s2op_mem_35, s2op_mem_36, s2op_mem_37, s2op_mem_38, s2op_mem_39, s2op_mem_40, s2op_mem_41, s2op_mem_42, s2op_mem_43, s2op_mem_44, s2op_mem_45, s2op_mem_46, s2op_mem_47, s2op_mem_48, s2op_mem_49, s2op_mem_50, s2op_mem_51, s2op_mem_52, s2op_mem_53, s2op_mem_54, s2op_mem_55, s2op_mem_56, s2op_mem_57, s2op_mem_58, s2op_mem_59, s2op_mem_60, s2op_mem_61, s2op_mem_62, s2op_mem_63, s2op_mem_64, s2op_mem_65, s2op_mem_66, s2op_mem_67, s2op_mem_68, s2op_mem_69, s2op_mem_70, s2op_mem_71, s2op_mem_72, s2op_mem_73, s2op_mem_74, s2op_mem_75, s2op_mem_76, s2op_mem_77, s2op_mem_78, s2op_mem_79, s2op_mem_80, s2op_mem_81, s2op_mem_82, s2op_mem_83, s2op_mem_84, s2op_mem_85, s2op_mem_86, s2op_mem_87, s2op_mem_88, s2op_mem_89, s2op_mem_90, s2op_mem_91, s2op_mem_92, s2op_mem_93, s2op_mem_94, s2op_mem_95, s2op_mem_96, s2op_mem_97, s2op_mem_98, s2op_mem_99, s2op_mem_100, s2op_mem_101, s2op_mem_102, s2op_mem_103, s2op_mem_104, s2op_mem_105, s2op_mem_106, s2op_mem_107, s2op_mem_108, s2op_mem_109, s2op_mem_110, s2op_mem_111, s2op_mem_112, s2op_mem_113, s2op_mem_114, s2op_mem_115, s2op_mem_116, s2op_mem_117, s2op_mem_118, s2op_mem_119]

#print axioms s2op_mem

end LatticeVOA
end HaagerupIzumi.C8
