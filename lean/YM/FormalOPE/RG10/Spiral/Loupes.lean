import YM.FormalOPE.RG10.Spiral.Lever
/-!
# Exhausting the unrestricted cover for signed-symbol proof.
One arbitrary test of a cover curl contour (later a Snap function) can be priced on a high
enough torus. No estimate of symbol rates assumed. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Spiral
open Function Wilson Lattice Gauge Precision Exterior Work.F03 Further.CorrectedLift.Compass Source.Drops
   PertExtension Filter RG PertExtension.LatticePT LatticePT.Projection Finset
open Next.Rank Hue Normal MvPolynomial AnalyticBridge.CouplingShape
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge}
local notation "Ω" => Hue.Panel RG.Slot G
abbrev Palms (G:Gauge):=Links ℤ G.Color
abbrev approaching := (atTop : Filter ℕ)
local notation "T" => side 3

private lemma wrap_at (p:Cover) : ∀ᶠ k in approaching,Lattice.lift (wrap (T k) p)=p := by
 have hp (m:ℕ): m≤3^m:= Nat.le_of_lt (Nat.lt_pow_self (by norm_num)) -- check
 have he i : ∀ᶠ k in approaching, -(↑((T k).val):ℤ)< 2*p i ∧ 2*p i≤(↑((T k).val):ℤ):= by
   filter_upwards [eventually_ge_atTop (2*(p i).natAbs)] with k hk
   have HH: k<(T k).val:= by
      change k<8*3^(k+1)*3^(k^2)
      have hh : 0<3^(k^2):= by positivity
      nlinarith [hp (k+1)]
   omega
 filter_upwards [eventually_all.mpr he] with k hk; exact lift_eq_iff.mpr ⟨rfl,hk⟩

def settle (X:Palms G)(v: Slot) :G.Color:=Exterior.linkSum X v.offset (square v.plaq.val.1 v.plaq.val.2)
private def arriving (X:Palms G)(t:ℕ): Bid.Dir G (T t):= windDir (n:=T t) (fun e=>X (Lattice.lift e.1,e.2))
private lemma read_i (X:Palms G)(v:Ω) : ∀ᶠ k in approaching, Spiral.tone (see v) (arriving X k) = (settle X v.1) v.2 := by
 let p:=v.1.offset
 filter_upwards [wrap_at p, wrap_at (p+Lattice.step v.1.plaq.val.1), wrap_at (p+Lattice.step v.1.plaq.val.2)] with k hk hi hj
 unfold settle; rw [orientedSum]; unfold Spiral.tone; rw [rawCoil,arriving,collect_wind]; unfold crease Orb.Curl see Converter.position; dsimp only; unfold p at hk hi hj; simp_rw [map_add,wrap_step] at hi hj; rw [hk,hi,hj] 
private lemma charges (X:Palms G)(p:poly Ω): ∀ᶠ k in approaching, readOn (arriving X k) p= Hue.display (settle X) p:= by
 induction p using MvPolynomial.induction_on with
 | C a=> exact Eventually.of_forall (fun k=> by simp [readOn,display])
 | add a b ht hw=> filter_upwards [ht,hw] with k ha hb; rw [map_add,map_add,ha,hb]
 | mul_X a i ha=> filter_upwards [ha, read_i X i] with k ha hi; rw [map_mul,map_mul,ha]; unfold readOn display; rw [aeval_X,aeval_X,hi]

lemma decipher (P:poly Ω)(X : Palms G): Tendsto (fun k=> readOn (arriving X k) (milk (rig (T k)) P)) approaching (𝓝 (Hue.display (settle X) (milk (covarianceSymbol G) P))) := by
 let Q k:= milk (rig (T k)) P
 have hp:= PolyFlow.milk_continuity (f:=fun _=>P) (K:=fun k =>rig (T k)) (fun i j=> landing 3 (by decide) i j) (PolyFlow.Limit.const)
 apply (hp.inspect (L:=(Hue.display (settle X)).toLinearMap)).congr'
 obtain ⟨z,-,hs⟩:= hp.fence
 filter_upwards [hs,eventually_all_finset z|>.mpr (fun i _=> charges X (monomial i 1))] with k hk hm
 change Hue.display _ (Q k)=readOn _ (Q k); have ht:= PolyFlow.terms (p:=Q k) hk
 rw (occs:=.pos [1,2]) [ht]; rw [map_sum,map_sum]; apply sum_congr rfl; intro i hi; rw [map_smul,map_smul,hm i hi]
theorem onCover {p q : poly Ω} (h:∀ n, ∀ v : Bid.Dir G n, readOn v p= readOn v q)(x:Palms G) : display (settle x) (milk (covarianceSymbol G) p)=display (settle x) (milk (covarianceSymbol G) q):= by
 have hi:= decipher p x; simp_rw [projectedHeat (h _)] at hi; exact tendsto_nhds_unique hi (decipher ..)
end YM.FormalOPE.RG10.Spiral
