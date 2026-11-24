import YM.Integration.WilsonThermometerUnitFilingWeakStrip
import YM.Integration.WilsonOriginalCompoundVertexStrip

/-! The actual interacting vertex with one exposed leg. The remaining angular legs are summed at their original translated sites. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakTrunk
open Function Filter Finset Lattice Laurent Bloch Precision RG Next.Free Work.F08
open AllOrder AllOrder.Floe Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding WilsonOriginalCompoundStrip FormalBulk08 RG.Supply Input
open scoped Classical BigOperators
variable {G:Gauge} {α E:Type*} [NormedAddCommGroup E]

def coat (s:ℝ)(o:Cover){k:ℕ}(z:Fin k→Cloth α):ℝ:=
  ∏i:Fin k,Real.exp (s*size ((z i).1-o))

theorem salary {k:ℕ}{σ s B:ℝ}(x:Cloth α)(o:Cover)(V:Ten E (Cloth α) (k+1))
    (trunk:cent x V 0 σ B)(sp:0 ≤ s)(width:(k:ℝ)*s ≤ σ):
    SumBudget (fun z:Fin k→Cloth α=>coat s o z*‖V (Fin.cons x z)‖)
      (Real.exp ((k:ℝ)*s*size (x.1-o))*B):=by
  let charge:=Real.exp ((k:ℝ)*s*size (x.1-o))
  have reserve:SumBudget (fun z:Fin k→Cloth α=>Real.exp (σ*soar terrain (Fin.cons x z))*‖V (Fin.cons x z)‖) B:=by
    simpa only [cent,pow_zero,one_mul] using trunk
  apply budget_minor (cap_scale reserve (Real.exp_pos _).le)
    (g:=fun z=>charge*(Real.exp (σ*soar terrain (Fin.cons x z))*‖V (Fin.cons x z)‖))
  · exact fun z=>mul_nonneg (prod_nonneg fun i _=>(Real.exp_pos _).le) (norm_nonneg _)
  intro z
  let D:=soar terrain (Fin.cons x z)
  have each (i:Fin k):Real.exp (s*size ((z i).1-o)) ≤ Real.exp (s*(size (x.1-o)+D)):=by
    apply Real.exp_monotone
    apply mul_le_mul_of_nonneg_left _ sp
    have near:terrain.gap x.1 (z i).1 ≤ D:=leg_le terrain (Prod.fst ∘ (Fin.cons x z:Fin (k+1)→Cloth α)) 0 i.succ
    have t:=terrain.tri o x.1 (z i).1
    exact_mod_cast (t.trans (Nat.add_le_add_left near _))
  have total:coat s o z ≤ charge*Real.exp (σ*D):=by
    apply (prod_le_prod (fun _ _=>(Real.exp_pos _).le) (fun i _=>each i)).trans
    simp only [prod_const,card_univ,Fintype.card_fin,←Real.exp_nat_mul,charge,←Real.exp_add]
    apply Real.exp_monotone
    nlinarith only [mul_nonneg (sub_nonneg.mpr width) (show 0 ≤ (D:ℝ) from Nat.cast_nonneg _)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right total (norm_nonneg (V (Fin.cons x z)))

theorem coupon (Q:Request G)(K:KernelChoices)(j H:ℕ):
    WilsonThermometerUnitFilingWeakStrip.trial Q K j H ≤ width Q K j H:=by
  apply min_le_min_left
  apply div_le_div₀ (Q.positive ..).le (min_le_left ..)
    (mul_pos (by norm_num) (Q.grows H))
  exact mul_le_mul_of_nonneg_left (le_max_right ..) (by norm_num)

theorem original (Q:Request G)(R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (paid:FundedMarkedCoverRows.prices v R.kit)(e:ℕ):
    ∀ᶠ first:ℕ in atTop,∃ V:Realm G (e+1) Credit.leanC,V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧
      V.anchor=first ∧ ∀i (_hi:V.anchor ≤ i) H,
      let A:=R.family.path.levels
      let μ:=WilsonThermometerUnitFilingWeakStrip.trial (WilsonOriginalCompoundVertexStrip.narrowed Q)
        R.metals.p.kernel (A.clock.J i) H
      ∀a (ha:a ≤ e+1) k N, i ≤ N → ∀t:ℝ,0≤t → t≤μ → ∀ x:YForest G,∀o:Cover,
        SumBudget (fun z:Fin k→YForest G=>coat (t/(k+1)) o z*‖actionW A R.metals.O N i a (k+1) (Fin.cons x z)‖)
         (Real.exp (t*size (x.1-o))*
          (WilsonOriginalCompoundVertex.tariff G e a k 0 ha).buy (Borough.ageZ (A.clock.hatBeta i))):=by
  filter_upwards [WilsonOriginalCompoundVertexStrip.original Q R simple v paid e] with first bought
  obtain ⟨V,draws,coins,_,anchor,all⟩:=bought
  refine ⟨V,draws,coins,anchor,?_⟩
  intro i hi H A μ a ha k N iN t sp tm x o
  obtain ⟨_,_,room,stock⟩:=all i hi
  have h:=((stock a ha k 0 N N iN le_rfl).2.2.1 x).main
  have cap:t ≤ (V.mint i hi).σ/2:=tm.trans ((coupon ..).trans (room H))
  have scaled:(k:ℝ)*(t/(k+1)) ≤ t:=by
    calc _=t*((k:ℝ)/(k+1)):=by ring
         _ ≤ t*1:=mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr (by linarith)) sp
         _=t:=mul_one _
  have offer:=salary x o _ h (div_nonneg sp (by positivity)) (scaled.trans cap)
  refine ⟨offer.1,offer.2.1,offer.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ ((tsum_nonneg h.1).trans h.2.2)
  exact Real.exp_monotone (mul_le_mul_of_nonneg_right scaled (Nat.cast_nonneg _))

end YM.Integration.WilsonThermometerUnitFilingWeakTrunk
