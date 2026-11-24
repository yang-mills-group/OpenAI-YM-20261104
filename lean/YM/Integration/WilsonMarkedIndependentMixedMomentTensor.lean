import YM.Integration.WilsonMarkedIndependentMixedMomentPrice

/-! A coupled angular row on the authentic finite period and on the cover.
Every price is uniform in the ultraviolet cutoff at fixed reporting inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedMomentTensor
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open WilsonMarkedIndependentMixedMomentPrice (Earned)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{m e:ℕ}{n:ℕ→Side}{t:ℕ→ℝ}

def Tensor (G:Gauge)(V:Type)[NormedAddCommGroup V](m e:ℕ)(n:ℕ→Side)(t:ℕ→ℝ)(Y:ℕ→Era G V):Prop:=
  ∀i≤e,∀r,∀x:Fin r→YForest G,Earned m t (fun N p=>(Y N).1 (n p) i r (slideC (n p) x))
    (fun N _=>(Y N).2 i r x)

theorem logged [DecidableEq ι]{D:ι→ℕ}{Y:ℕ→Outerm G D}{s B:ℝ}
    (growth:Tendsto (fun p=>(n p).val) atTop atTop)(width:0<s)(budget:1≤B)
    (old:∀ᶠp:ℕ in atTop,∀N,m≤N → PairedAt e (Y N) (n p) s B)
    (q:ι → Cover)(I:Finset ι):
    Tensor G (Pen D I) m e n (fun p=>catchW s (n p)) (fun N=>Y N q I):=by
  intro i hi r x
  have price:0≤B^I.card:=pow_nonneg (zero_le_one.trans budget) _
  refine ⟨B^I.card,price,?_⟩
  filter_upwards [old,growth.eventually_ge_atTop (4*Syn terrain q I x+1)] with p kernel large
  intro N live
  have pair:=kernel N live q I i hi r
  refine ⟨(pair.bill.2 _).trans ?_,(pair.access.2 _).trans ?_,pair.gulf.local_w x (by omega)⟩
  all_goals apply mul_le_of_le_one_right price;apply Real.exp_le_one_iff.mpr;exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr width.le) (Nat.cast_nonneg _)

theorem puffed [DecidableEq ι](D:ι→ℕ)(ht:∀p,0≤t p):
    Tensor G (Pen D ∅) m e n t (fun _=>puff D G):=by
  intro i _ r x
  have h(p:ℕ):((puff D G).1 (n p) i r (slideC (n p) x))=(puff D G).2 i r x:=by
    change (uband 1 i r (slideC (n p) x)) • ochre D=(uband 1 i r x) • ochre D
    by_cases hr:0=r
    · subst r;rfl
    · simp [uband,shine_dark hr]
  simp_rw [h];exact WilsonMarkedIndependentMixedMomentPrice.constant m t ht _

omit [NormedSpace ℝ V] in
theorem zero (ht:∀p,0≤t p):Tensor G V m e n t (fun _=>0):=
  fun _ _ _ _=>WilsonMarkedIndependentMixedMomentPrice.constant m t ht 0

theorem smul {Y:ℕ→Era G V} (c:ℝ)(h:Tensor G V m e n t Y):
    Tensor G V m e n t (fun N=>c • Y N):=fun i hi r x=>
  WilsonMarkedIndependentMixedMomentPrice.smul c (h i hi r x)

omit [NormedSpace ℝ V] in
theorem sum {α:Type}(S:Finset α)(Y:α→ℕ→Era G V)(ht:∀p,0≤t p)(h:∀u∈S,Tensor G V m e n t (Y u)):
    Tensor G V m e n t (fun N=>∑u∈S,Y u N):=by
  intro i hi r x
  simp only [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply]
  exact WilsonMarkedIndependentMixedMomentPrice.summed ht S _ _ fun u hu=>h u hu i hi r x

end YM.Integration.WilsonMarkedIndependentMixedMomentTensor
end
