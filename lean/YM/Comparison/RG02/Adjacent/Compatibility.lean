import YM.Comparison.RG02.Adjacent.Caliber
/-!
# Clocks through changing order. Compatibility of resetting before/after projection

Enlarge the finite order: coherent re-expression. Different kinetic readout schemes or profiles
on differing regulators can't use `compatible` without SEEING their readout through those
orders. No convergence or all-mesh clocks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice Marker Multi
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
local notation "φ"=> 𝓝 (0:ℝ)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {r:ℕ}

structure Riding (r:ℕ)(f g:ℝ→X) : Prop where
  left : ContDiffAt ℝ ω f 0
  right : ContDiffAt ℝ ω g 0
  agrees i : i≤r → iteratedFDeriv ℝ i f 0=iteratedFDeriv ℝ i g 0

namespace Riding
variable {f g h:ℝ→X}
lemma here (u : Riding r f g): f 0=g 0:= by simpa only [iteratedFDeriv_zero_apply] using congrArg (fun P : T ℝ X 0=> P (fun _ =>1)) (u.agrees 0 (Nat.zero_le _))
lemma same (h : ContDiffAt ℝ ω f 0)(hu:f=ᶠ[φ]g): Riding r f g := ⟨h,h.congr_of_eventuallyEq hu.symm, fun i _=> (hu.iteratedFDeriv ℝ i).eq_of_nhds⟩
lemma mirror (u : Riding r f g): Riding r g f := ⟨u.right,u.left,fun _ hi=> (u.agrees _ hi).symm⟩
lemma twice (u:Riding r f g)(v:Riding r g h): Riding r f h:= ⟨u.left,v.right,fun _ hi=> (u.agrees _ hi).trans (v.agrees _ hi)⟩
lemma shadow {f g:ℝ→ℂ}: Riding r f g ↔ Shadow r f g := by
   constructor
   · intro u; refine ⟨u.left,u.right,fun i hi=>?_⟩; unfold motion Assembly.jet; rw [u.agrees i hi]
   intro u; refine ⟨u.left,u.right,fun i hi=>?_⟩; ext; exact (smul_right_inj (show ( (i.factorial:ℝ)⁻¹)≠0 from by positivity)).mp (u.aligns i hi)
lemma respite (u:Riding r f g)(K:UnitCost): Riding r (f ∘ K.enter) (g ∘ K.enter) := by
   have hp : ContDiffAt ℝ ω f (K.enter 0):= by rw [K.borne]; exact u.left
   have hq : ContDiffAt ℝ ω g (K.enter 0):= by rw [K.borne]; exact u.right
   refine ⟨hp.comp _ K.here,hq.comp _ K.here,fun i hi=>?_⟩; rw [iteratedFDeriv_comp hp K.here le_top,iteratedFDeriv_comp hq K.here le_top, K.borne]
   unfold FormalMultilinearSeries.taylorComp; apply Finset.sum_congr rfl; intro c _; refine ContinuousMultilinearMap.ext fun v=>?_
   simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]; rw [u.agrees _ (c.length_le.trans hi)]
lemma lifts (u:Riding r f g) {s:X→Y} (h:ContDiffAt ℝ ω s (f 0)): Riding r (s ∘ f) (s ∘ g):= by
   have hu:ContDiffAt ℝ ω s (g 0):= u.here ▸ h
   refine ⟨h.comp _ u.left,hu.comp _ u.right,fun i hi=>?_⟩
   rw [iteratedFDeriv_comp h u.left le_top,iteratedFDeriv_comp hu u.right le_top,u.here]; unfold FormalMultilinearSeries.taylorComp
   apply Finset.sum_congr rfl; intro c _; refine ContinuousMultilinearMap.ext fun v=> ?_; simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]
   apply congrArg; funext i; rw [u.agrees _ ((c.partSize_le i).trans hi)]
lemma realLife {f g:ℝ→ℝ}: Riding r f g ↔ Shadow r (fun x=> (f x:ℂ)) (fun x=> (g x:ℂ)):= by
   constructor; · exact fun u => shadow.mp (u.lifts Complex.ofRealCLM.contDiff.contDiffAt)
   exact fun u=> ((shadow.mpr u).lifts Complex.reCLM.contDiff.contDiffAt)
end Riding

namespace Share
variable {K L : UnitCost} {p q : Caliber}
def Recommend (r:ℕ)(K L:UnitCost): Prop:= Riding r K.rating L.rating
private lemma enter_price (K: UnitCost)(i:ℕ): motion (fun x=> (K.enter x:ℂ)) i=if 1≤ i then motion (fun x=> (K.rating x:ℂ)) (i-1) else 0:= by
   have h:= K.smooth; simp only [UnitCost.enter, Complex.ofReal_mul]; simpa only [pow_one] using mono_price (f:=fun x=> (K.rating x:ℂ)) (n:=i) (k:=1) (Complex.ofRealCLM.contDiff.contDiffAt.comp _ h)
lemma tariff : Recommend r K L ↔ Riding (r+1) K.enter L.enter := by
   rw [Riding.realLife, Recommend, Riding.realLife]; constructor
   · intro u; refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp _ K.here,Complex.ofRealCLM.contDiff.contDiffAt.comp _ L.here,fun i hi=>?_⟩; rw [enter_price,enter_price]; split; · rw [u.aligns _ (by omega)]
     rfl
   intro u; refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp _ K.smooth,Complex.ofRealCLM.contDiff.contDiffAt.comp _ L.smooth,fun i hi=>?_⟩; have hh:= u.aligns (i+1) (by omega); rwa [enter_price,enter_price,if_pos (by omega), if_pos (by omega),Nat.add_sub_cancel] at hh
lemma direction (u: Recommend r K L) : Recommend r K.inverseCurve L.inverseCurve:= by
   rw [tariff]; let l:= L.inverseCurve;let k:=K.inverseCurve
   have hu:= (tariff.mp u).respite l
   have ht:= (Riding.same (r:=r+1) hu.right L.rightInverse.stairs)
   have hv : ContDiffAt ℝ ω k.enter ((K.enter∘l.enter) 0):= by simp [k.here]
   have hh:= (hu.twice ht).lifts hv
   exact hh.mirror.twice (Riding.same hh.left (K.rightInverse.pairs.comp_tendsto l.roots))
lemma reader {v:ℕ} (h:r≤v)(hp:∀ i≤r,p.measure i=q.measure i): Recommend r (p.direct r) (q.direct v) := by
   have h00 (p:Caliber)(r:ℕ)(i:ℕ): motion (fun t=> (p.tariff r t:ℂ)) i=if i≤r then (p.measure i:ℂ) else 0:= by
       unfold Caliber.tariff; simp_rw [Complex.ofReal_sum, Complex.ofReal_mul,Complex.ofReal_pow]
       rw [show (fun t:ℝ=> ∑ i∈ range (r+1), (t:ℂ)^i*(p.measure i:ℂ))= _ from (show peval (fun i=> (p.measure i:ℂ)) r = _ from funext fun t=> by simp_rw [peval,Zone.eval,Complex.real_smul,Complex.ofReal_pow]).symm]; exact polary _ i r
   have hv:Riding r (p.tariff r) (q.tariff v):= by
       apply Riding.realLife.mpr; refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((p.smooth _).contDiffAt), Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((q.smooth _).contDiffAt), fun i hi=>?_⟩; rw [h00,h00,if_pos hi,if_pos (hi.trans h),hp i hi]
   exact hv.lifts (s:=fun t:ℝ=> (Real.sqrt t)⁻¹) ((contDiffAt_id.sqrt (by simp [p.zero_tariff])).inv (by simp [p.zero_tariff]))
lemma money_part (u : Recommend r K L)(d:ℤ)(i k:ℕ): Shadow r (money K d i k) (money L d i k):= by
   let f:= tags d i k; have hs : ContDiffAt ℝ ω f 1:= by
      unfold f; have hp:  (fun t:ℝ=> tags d i k t)=ᶠ[𝓝 1] fun t=> t^(d+i-k) := (lt_mem_nhds (show (0:ℝ)<1 from zero_lt_one) : ∀ᶠ t : ℝ in 𝓝 1,0<t).mono fun t ht=> exchange d i k ht.ne'
      rcases he : d+i-k with h | h
      -- substitute valuation
      all_goals rw [he] at hp
      · exact (contDiffAt_id.pow h).congr_of_eventuallyEq (by simpa only [Int.ofNat_eq_natCast,zpow_natCast] using! hp)
      exact ((contDiffAt_id.pow (h+1)).inv (by simp)).congr_of_eventuallyEq (by simpa only [zpow_negSucc] using! hp)
   exact (Shadow.refl ((Complex.ofRealCLM.contDiff.contDiffAt).pow i)).product (Riding.realLife.mp (Riding.lifts (s:=f) u (K.origin.symm ▸ hs)))

lemma born_commutes {m:ℕ→ℤ}{P Q : Display X}{s:ℕ} {i:ℕ}
   (u:Recommend r K L)(d:ℤ)(he:i≤r)(hv:r≤ s)(hK:Charge r m P)(hL:Charge s m Q)(hp:∀ j≤ r,P j=Q j): born P K d r i=born Q L d s i := by
   funext x; rw [ledger K d r hK _ he,ledger L d s hL _ (he.trans hv),hp i he]; refine congr_arg₂ _ rfl (sum_congr rfl fun j hj=>?_) -- compare via same m
   have hh:= lt_of_lt_of_le (mem_range.mp hj) he; rw [hp j hh.le]; refine sum_congr rfl fun k hk=>?_; rw [(money_part u d j k).aligns i he]
end Share
end YM.Comparison.RG02.Adjacent
