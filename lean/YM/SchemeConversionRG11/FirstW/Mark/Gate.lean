import YM.SchemeConversionRG11.FirstW.Mark.Letter
/-! Scalar difference tape for open direct slot, needed also as distributions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Pert.Align Topology Maxwell
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {j : ℕ}
def canal (k : Labels.Key G) (o : Site n) : FullT G n := tbranch G n (native k o)
def river (h : ℝ) (k : Labels.Key G) (o : Site n) := (h^(mass k))⁻¹ • canal k o
lemma gauged (h : ℝ) (k : Labels.Key G) (o : Site n) : river h k o=tbranch G n (tape k h o) := by rw [tape_scales,map_smul];rfl
lemma stampGreen (a : Atom j) (z : Site n) : ∑ t, a.degree t * linGreen n (z-wrap n (a.offset t)) = a.orientation false * combine a.dirs (linGreen n) (z+wrap n (a.foot false)) := by
  have he : (∑ t:Atom.Kind j,(a.degree t:ℂ) * Full.toroid (z-wrap n (a.offset t))) = (a.orientation false : ℝ) * combine a.dirs (@Full.toroid n) (z+wrap n (a.foot false)) := by
    unfold Full.toroid -- breaks combine rhs, need keep
    -- restore
    change (∑ t:Atom.Kind j,(a.degree t:ℂ) * ∑ v:Site n,_)= (a.orientation false : ℝ) * combine _ (@Full.toroid n) _
    rw [combine_green]
    conv_lhs => simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _
    have h := a.phaseA p false
    simp only [Atom.coverMul,Bool.false_eq_true,if_false,map_neg] at h
    simp_rw [sub_eq_add_neg,Full.char_add]
    simp_rw [show ∀ t:Atom.Kind j,(a.degree t:ℂ) * (Full.topWeight n p * (Full.char p z * Full.char p (-wrap n (a.offset t)))) = Full.char p z * Full.topWeight n p * ((a.degree t:ℂ)*Full.char p (-wrap n (a.offset t))) from fun t=>by ring] -- rw not simp under binder?
    rw [←Finset.mul_sum,h]; ring
  have hv := congrArg Complex.reCLM he; rw [map_sum] at hv
  have hh (x : Site n): combine a.dirs (linGreen n) x=(combine a.dirs (@Full.toroid n) x).re := congrFun (combine_map _ Complex.reLm.toAddMonoidHom _) x
  rw [hh]; simpa only [linGreen,Complex.reCLM_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hv
lemma sector_gate (u : G.Color) (x y : Site n) (a : Atom j) (i : Axis) :
    tbranch G n (eman x a u) (y,i) = (a.orientation false * combine a.dirs (linGreen n) (y-x+wrap n (a.foot false))) • (if i=a.rotated then u else 0) := by
  rw [← stampGreen]; simp only [eman,map_sum,map_smul,branch_at, Finset.sum_apply,Pi.smul_apply,Orb.ghostLink, Atom.edgePull]; split_ifs; swap; · simp
  rw [Finset.sum_smul]; refine Finset.sum_congr rfl (fun t _=>?_); rw [smul_smul,sub_sub]; rfl
variable (k : Labels.Key G)
abbrev QuotSpot (k : Labels.Key G) := Signed × Spot G k.1 × Bool
def RepA (v : QuotSpot k) : Atom k.1 := if v.2.2 then (v.2.1.atom v.1) else Align.swap (v.2.1.atom v.1)
def header (v : QuotSpot k) (i : Axis) := let q:=RepA k v; let e:=billed v.1 k.2 v.2.1; (if v.2.2 then e * q.orientation false else -(e*q.orientation false)) • (if i=q.rotated then unitColor G v.2.1.color else 0)
def rivDir (v : QuotSpot k) := (RepA k v).dirs
def footA (v : QuotSpot k) := (RepA k v).foot false
lemma riv_mass (v : QuotSpot k) : (rivDir k v).length + 1=mass k := by rw [rivDir,Atom.length_dirs];rfl
lemma repr_river (o : Site n) (v : Site n) (i : Axis) :
    canal k o (v,i)=∑ t:QuotSpot k, combine (rivDir k t) (linGreen n) (v-o + wrap n (footA k t)) • header k t i := by
  rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type,Fintype.sum_bool]; rw [canal,letter_exact]; simp only [map_sum,map_smul,map_sub, Finset.sum_apply,Pi.smul_apply,Pi.sub_apply]; refine Finset.sum_congr rfl (fun s _=>Finset.sum_congr rfl fun hp _=>?_); simp only [sector_gate,header, RepA,rivDir,footA]; simp only [Bool.false_eq_true,↓reduceIte,smul_sub,smul_smul, neg_smul];
  rw [smul_neg,smul_smul,←sub_eq_add_neg]; congr 2 <;> ring
lemma carried (o : Site n) (v : Site n) (i : Axis) : canal k o (v,i)=canal k (0:Site n) (v-o,i) := by rw [repr_river,repr_river]; simp only [sub_zero]
end YM.RG11.FirstW
