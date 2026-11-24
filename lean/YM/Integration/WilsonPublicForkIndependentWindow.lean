import YM.Integration.WilsonPublicForkIndependentDecay

/-! Ordinary far reading of the normalized independent product on a
polynomial window, including the full projected row at each retained weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentWindow
open Filter Function Set Finset PowerSeries FVA2 FVA2.O FVA2.O.Score FVA2.O.Enh
open FVA2.O.Project FVA2.Scale FVA2.Register Maxwell XSpace XSpace.Normalize
open MS MS.Land MS.Fleet MS.Theater MS.Rake
open WilsonMSDictionaryFarRead WilsonPublicForkIndependentDecay
open scoped Classical Topology BigOperators
variable {G:Gauge}{n m h:ℕ}
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

abbrev canon (Z:WilsonPrescription G):=Measure.outlook Z.scheme Z.criterion
abbrev joint (Z:WilsonPrescription G)(u:Scan G n)(v:Scan G m)(x:Points n)(y:Points m)(s:ℝ):=
  party (install (canon Z)) x (squeeze (-s) y) u v
abbrev leg (Z:WilsonPrescription G)(v:Scan G m)(b:Dframe.Toon G h)(y:Points m)(s:ℝ):=
  lonelyG (install (canon Z)) (squeeze (-s) y) (Dframe.flash b) v
abbrev front (Z:WilsonPrescription G)(u:Scan G n)(b:Dframe.Toon G h)(x:Points n):=
  Canon.FarCoefficients (canon Z) u x (Dframe.flash b)

def contrast (h q:ℕ)(τ:ℝ)(u:Scan G n)(v:Scan G m)(x:Points n)(y:Points m)(s:ℝ):ℂ:=
  fee s (-(totalG v:ℝ))*(cutoff q (measuring τ s) (joint Z u v x y s)-
  ∑ b:Dframe.Toon G h,cutoff q (measuring τ s) (front Z u b x)*cutoff q (measuring τ s) (leg Z v b y s))

private theorem cut_sub (q:ℕ)(t:ℝ)(a b:PowerSeries ℂ):
    cutoff q t (a-b)=cutoff q t a-cutoff q t b:=by
  simp [cutoff,mul_sub,Finset.sum_sub_distrib]

private theorem cut_sum {J:Type}[Fintype J](q:ℕ)(t:ℝ)(f:J→PowerSeries ℂ):
    cutoff q t (∑j,f j)=∑j,cutoff q t (f j):=by
  unfold cutoff;simp only [map_sum,Finset.mul_sum];rw [Finset.sum_comm]

include ν ms in
theorem original (h q:ℕ)(τ:ℝ)(tp:0≤τ)(u:Scan G n)(v:Scan G m)
    (K:Set (Points n))(closed:IsCompact K)(inside:K⊆conf n)
    (L:Set (Points m))(far:IsCompact L)(outside:L⊆Outside m):
    Rain (min ((h:ℝ)+1) (τ*(q+1))) (fun (i:K×L) s=>contrast Z h q τ u v i.1 i.2 s):=by
  let d:ℝ:=totalG v
  let e:=min ((h:ℝ)+1) (τ*(q+1))
  let α:=fun (b:Dframe.Toon G h) (i:K×L) (_:ℝ)=>front Z u b i.1
  let β:=fun (b:Dframe.Toon G h) (i:K×L) (s:ℝ)=>leg Z v b i.2 s
  let Ω:=install (canon Z)
  let F:=Canon.FarCoefficients (canon Z) u
  let Q:=fun (i:K×L) s=>Basket Ω u v (F i.1) h i.1 (squeeze (-s) i.2)
  have source:=(ms.separatedOPE ν).wilson
  have bound:Rain (d+e) (fun (i:K×L) s=>cutoff q (measuring τ s) (Q i s)):=by
    have hQ:ChargeP (q+1) ((h:ℝ)+1+d) Q:=(source.far u).2.2 K closed inside h (q+1) m L v far outside
    apply (evaluation q τ tp hQ).size;dsimp [e];linarith [min_le_left ((h:ℝ)+1) (τ*(q+1))]
  have tail(b:Dframe.Toon G h):Rain (d+e) (fun (i:K×L) s=>
      cutoff q (measuring τ s) (α b i s)*cutoff q (measuring τ s) (β b i s)-
      cutoff q (measuring τ s) (α b i s*β b i s)):=by
    have near:ChargeP (q+1) 0 (α b):=by
      intro k _
      have cont:ContinuousOn (fun x=>coeff k (F x (Dframe.flash b))) K:=((source.far u).2.1 _ k).mono inside
      obtain ⟨c,cap⟩:=closed.exists_bound_of_continuousOn cont
      exact Rain.cash ⟨c,fun i=>cap i.1 i.1.property⟩
    have dst:ChargeP (q+1) d (β b):=by
      have hire:=Uniform.teeth_P source.scope source.dimensions far outside source.awake v (Dframe.flash b) (q+1)
      intro k hk
      exact ((hire k hk).pull (fun i:K×L=>i.2)).size (le_add_of_nonneg_left (Nat.cast_nonneg _))
    apply (overshoot q τ tp near dst).size;dsimp [e];linarith [min_le_right ((h:ℝ)+1) (τ*(q+1))]
  have families:=Rain.sum Finset.univ (fun b _=>tail b)
  have algebra(i:K×L)(s:ℝ):
      cutoff q (measuring τ s) (joint Z u v i.1 i.2 s)-∑b,cutoff q (measuring τ s) (α b i s)*cutoff q (measuring τ s) (β b i s)=
      cutoff q (measuring τ s) (Q i s)-∑b,(cutoff q (measuring τ s) (α b i s)*cutoff q (measuring τ s) (β b i s)-
        cutoff q (measuring τ s) (α b i s*β b i s)):=by
    dsimp only [Q,Basket]
    rw [←LampT,cut_sub,cut_sum,Finset.sum_sub_distrib]
    change _=cutoff q (measuring τ s) (joint Z u v i.1 i.2 s)-
      ∑b,cutoff q (measuring τ s) (α b i s*β b i s)-
      ((∑b,cutoff q (measuring τ s) (α b i s)*cutoff q (measuring τ s) (β b i s))-
        ∑b,cutoff q (measuring τ s) (α b i s*β b i s))
    abel
  have raw:Rain (d+e) (fun (i:K×L) s=>cutoff q (measuring τ s) (joint Z u v i.1 i.2 s)-
      ∑b,cutoff q (measuring τ s) (α b i s)*cutoff q (measuring τ s) (β b i s)):=by
    simp_rw [algebra];exact bound.minus families
  have normed:=(Rain.all_fee (I:=K×L) (a:=-d)).mul raw
  have eq:-d+(d+e)=e:=by ring
  rw [eq] at normed
  exact normed

include ν ms in
theorem rate (h q U:ℕ)(τ:ℝ)(tp:0<τ)(space:τ*U<(h:ℝ)+1)(order:U<q+1)(u:Scan G n)(v:Scan G m)
    (K:Set (Points n))(closed:IsCompact K)(inside:K⊆conf n)
    (L:Set (Points m))(far:IsCompact L)(outside:L⊆Outside m):
    ∀ᶠ s in atTop,∀x∈K,∀y∈L,‖contrast Z h q τ u v x y s‖≤(measuring τ s)^U:=by
  have cap:=pays (original Z M ν ms h q τ tp.le u v K closed inside L far outside)
    (lt_min space (mul_lt_mul_of_pos_left (by exact_mod_cast order : (U:ℝ)<(q:ℝ)+1) tp))
  filter_upwards [cap] with s paid x hx y hy
  have e:(measuring τ s)^U=Real.exp (-(τ*U)*s):=by
    unfold measuring;rw [←Real.exp_nat_mul];congr 1;ring
  rw [e];exact paid (⟨x,hx⟩,⟨y,hy⟩)

end YM.Integration.WilsonPublicForkIndependentWindow
