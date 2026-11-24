import YM.Integration.WilsonIndependentSpoutMasterReport

/-! Both inverse clocks on the normalized measurement share a cutoff rate on the actual optical interval. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterBareClocks
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentSpoutScalarLedger (ground)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n h D k u e:ℕ}
section
open PowerSeries
variable {F:Labels.Frame G h}(H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W K:Credit)

lemma powers : ∃ V:Credit,∀ (t:CourseS H T p e E W K)(i j:ℕ),i≤ e→j≤e → let A:=t.vols; let B n:= relativeF A.draws A.paid n t.spur t.length; twain (V.buy t.Age) t.cab (coeff i ((B t.I.n)^j)) (coeff i ((B t.I.N)^j)):=by
    let S:= (Finset.range (e+1))×ˢ(Finset.range (e+1)); let P (k:ℕ×ℕ)(C:Credit): Prop:=∀ t:CourseS H T p e E W K, let A:=t.vols; let B n:= relativeF A.draws A.paid n t.spur t.length; twain (C.buy t.Age) t.cab (coeff k.1 ((B t.I.n)^k.2)) (coeff k.1 ((B t.I.N)^k.2))
    have H : ∀ i∈ S,∃ V:Credit,P i V:=by
       rintro ⟨i,j⟩ h; have hx:i < e+1:=Finset.mem_range.mp (Finset.mem_product.mp h).1
       let F (t:WindowS G (e+1) E) (n):= relativeF t.robe.draws t.robe.paid n t.base t.span
       obtain ⟨d,C,h,H⟩:= clipped_pow (WindowS.payments G (e+1) E) (i:=i) (p:=fun t:WindowS G (e+1) E=>F t t.n) (q:=fun t:WindowS G (e+1) E=> F t t.N) j (fun i g=> Bank.ascend G (e+1) i E (by omega))
       let V: Credit:= ⟨d,max 1 C,le_max_left ..⟩; refine ⟨V,?_⟩; intro t G J
       have hp :C*t.Age^d≤ V.buy t.Age:= mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans t.I.warm) _)
       have ht:= (H t.I).lift hp (trail_pos ..).le; dsimp only [F,Pi.pow_apply] at ht; rw [t.peace] at ht; exact ht
    obtain ⟨X,f⟩:= uniformPays (P:=P) S (fun i hi=> H i hi) (fun i _ x y v H=> by intro t A B; exact (H t).lift (v _ t.I.warm) (trail_pos ..).le); exact ⟨X,fun t i j v h=>f (i,j) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩) t⟩

end

def Paid (R:Run G)(j e:ℕ)(C:Credit):Prop:=
  let A:=R.family.path.levels
  ∀(m K i b:ℕ),j ≤ m → m ≤ K → i ≤ e → b ≤ e →
    ‖PowerSeries.coeff i ((relativeF A R.metals.O K m (K-m))^b)‖ ≤ C.buy (Compar A.S (zz A) m K)


theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)(cap:capP (deck (G:=G) l d admit)≤k):
    ∃C:Credit,∀ᶠ j:ℕ in atTop,Paid R j e C:=by
  let S:SectionData ((primes G).F h):=(primes G).T h
  obtain ⟨C,clock⟩:=powers (hol G) S p e Credit.leanC Credit.leanC Credit.leanC
  refine ⟨C,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap] with j joint
  obtain ⟨W,Y,levels,ratio,y,anchor,agrees,_⟩:=joint
  intro m K i b awake mK ie be
  let I:WindowS G (e+1) Credit.leanC:=
    ⟨Y.L.V,m,K-m,K,K,K,by simpa only [anchor] using awake,by omega,le_rfl,le_rfl⟩
  let B:CourseS (hol G) S p e Credit.leanC Credit.leanC Credit.leanC:=⟨W,I,by rw [agrees]⟩
  have grant:=(clock B i b ie be).main
  change ‖PowerSeries.coeff i ((relativeF W.arch.V.draws W.arch.V.paid K m (K-m))^b)‖ ≤ C.buy I.Age at grant
  dsimp only [I,WindowS.Age] at grant
  rw [agrees,levels,ratio,y,show m+(K-m)=K by omega] at grant
  exact grant
end YM.Integration.WilsonIndependentSpoutMasterBareClocks
end
