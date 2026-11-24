import YM.SchemeRG11.Wisp.Thyme
/-! WARD collapse on exact Taylor inputs. After cancellation in the shell expression remaining
 terms may be bounded by shell (for smooth windows) uniformly in field CT. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.North
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels
open scoped Classical Pointwise
variable {G:Gauge} {χ:Cover→ℝ}{s:Finset Cover} {m:ℕ}
def fringe (χ:Cover→ℝ)(s:Finset Cover)(θ:Cover→ G.Color):vellum G:= ∑ i∈parade s, leaf (brim χ i)*leaf (drift θ i)
def nudge (χ:Cover→ℝ)(s:Finset Cover)(θ:Cover→ G.Color):vellum G:=∑i∈parade s, χ i.1.1 • (leaf (radius i)*leaf (drift θ i))
lemma lineTariff (θ:Cover→G.Color)(h:covers χ s): vent (cant (ascent θ)) (escort χ s)= -(1/2:ℝ) • (nudge χ s θ+fringe χ s θ):=by rw [tariff χ s θ h]; unfold fringe nudge; simp only [edgeT,map_add,map_smul, add_mul,Finset.sum_add_distrib,smul_mul_assoc]
lemma silence (A:Bevy G.Color)(h:A∈team G.Color m)(χ:Cover→ℝ)(s:Finset Cover)(θ:Cover→ G.Color) : aeval (cant (linkup A)) (nudge χ s θ)=0:=by simp only [nudge,map_smul,map_sum,map_mul,Haze.realTaste]; rw [Finset.sum_eq_zero]; intro i hi; rw [radius_null i _ h,zero_mul,smul_zero]
lemma turnup_i (p:pLabel G)(i:Shaft G)(A:Bevy G.Color)(h:A∈team G.Color m)(θ:Cover→ G.Color):
 let D:=land G; let R:= leaf (drift θ i); let kap:=leaf (radius i); let q:=castZero 1 p
 aeval (cant (linkup A)) (D.heat (kap*R*q))=aeval (cant (linkup A)) (D.heat (R*vent (splinter i) q)):=by
 intro D R L q; unfold L; rw [mul_assoc,D.zephyr,map_add,map_mul,Haze.realTaste,radius_null i _ h,zero_mul,zero_add,D.wind]
 rw [vent_l,rear0] -- at R maybe
 rw [mul_zero,add_zero,final_d]; intro e; unfold q castZero; rw [lofts]
-- bill residual
lemma retort (p:pLabel G)(A:Bevy G.Color)(h:A∈team G.Color m)(χ:Cover→ℝ)(s:Finset Cover)(θ:Cover→ G.Color):
 aeval (cant (linkup A)) ((land G).heat (nudge χ s θ*castZero 1 p))=aeval (cant (linkup A)) ((land G).heat (∑ i∈parade s,χ i.1.1 • (leaf (drift θ i)*vent (splinter i) (castZero 1 p)))):=by
 rw [nudge,Finset.sum_mul]; simp only [smul_mul_assoc,map_sum,map_smul]; exact Finset.sum_congr rfl fun i _=> congrArg ((χ i.1.1:ℝ) • ·) (turnup_i p i A h θ)

def nebula (χ:Cover→ℝ)(s:Finset Cover)(p:pLabel G):vellum G:=
 (land G).heat (castFirst 1 p) + (escort χ s * stemZero 1 p - (land G).heat (escort χ s*castZero 1 p))
lemma withholds (χ:Cover→ℝ)(s:Finset Cover)(p:pLabel G): nebula χ s p=(land G).heat (castFirst 1 p) - ((land G).weave (escort χ s) (stemZero 1 p) - escort χ s *stemZero 1 p):=by
 unfold nebula Haze.Dose.weave; rw [castFree,show (land G).neg.heat (escort χ s)=escort χ s from Eq.trans (congrArg (land G).neg.heat (warm χ s).symm) ((land G).opposite _)]; abel
def gas (χ:Cover→ℝ)(s:Finset Cover)(p:pLabel G)(θ:Cover→G.Color): vellum G:= (1/2:ℝ) • ((land G).heat (fringe χ s θ*castZero 1 p)-fringe χ s θ * stemZero 1 p)
theorem zeroPoint (p:pLabel G): ∃ v:Finset (Shaft G),∀ (χ:Cover→ℝ)(s:Finset Cover), covers χ s→v⊆parade s → (∀i∈v,χ i.1.1=1)→∀ (θ:Cover→G.Color),θ 0=0 → ∀(m:ℕ)(A:Bevy G.Color),A∈team G.Color m → aeval (cant (linkup A)) (vent (cant (ascent θ)) (nebula χ s p)) = aeval (cant (linkup A)) (gas χ s p θ):=by
 obtain ⟨v,H⟩:= marked p; refine ⟨v,fun χ s h g ht θ he m A hp=>?_⟩
 unfold nebula gas; simp only [map_sub,map_add, (land G).wind, H χ s g ht θ he, vent_l,lineTariff θ h,lofts, (sailing 1 p (linkup A) θ he).1,mul_zero,zero_add,mul_smul_comm,map_smul]; simp only [map_mul,map_add,silence A hp χ s θ, zero_add]
 rw [mul_comm (castZero 1 p), add_mul,map_add,map_add,retort p A hp]; simp only [smul_eq_mul]; ring
-- shell expression requires no self contraction! important
lemma draft_free (θ:Cover→G.Color)(p:Shaft G): vent ((land G).windfall (brim χ p)) (leaf (drift θ p))=0:=by
 rw [taste]; rw [drift,map_sum]; suffices H: (∑ i:G.ColorIndex,_)= (0:ℝ) by rw [H,map_zero]
 apply Finset.sum_eq_zero; intro i _; rw [sense,Finsupp.linearCombination_single]
 by_cases h:i=p.2
 · subst i; rw [rand_c]; simp
 have he:(land G).windfall (brim χ p) (p.1,i)=0:=by
   rw [brim,map_sum,Finset.sum_apply]; apply Finset.sum_eq_zero; intro j _; rw [map_smul,Pi.smul_apply,intake,map_sum,Finset.sum_apply]; rw [Finset.sum_eq_zero _,smul_zero]
   intro k _; fin_cases k <;> simp [land, tongue,Haze.Dose.windfall,h,Ne.symm]
 rw [he,smul_zero]
lemma fringeHeat (θ: Cover→G.Color): (land G).heat (fringe χ s θ)=fringe χ s θ:=by
 unfold fringe; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [(land G).zephyr,(land G).lit,draft_free,add_zero]
end YM.SchemeRG11.North
