import YM.MSbar.Ballet.Glimpse
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
variable (i m s j p:ℕ)(V:StageCost)(a:ℝ)
lemma heightsP (ha:0<a) : ∀ᶠ n:ℕ in atTop,∀ P:Patch,P.L.val=n→mortgage V P m a:=by
   let f(n:ℕ):ℝ:=Cane.value 0 V.C V.A V.E V.s V.sway/n; have hv:Tendsto f atTop (𝓝 0):=tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
   have hx':∀ᶠ n:ℕ in atTop,∀ i∈ Icc (4:ℕ) m, climbV V i n<a:= (Icc _ _).eventually_all.mpr fun i he=> (height i V (mem_Icc.mp he).1).eventually (eventually_lt_nhds ha)
   have hx:∀ᶠ n:ℕ in atTop,∀ i∈Icc (1:ℕ) 3, plotV V i n<a:= (Icc _ _).eventually_all.mpr fun i he=> (depth i V he).eventually (eventually_lt_nhds ha)
   filter_upwards [hx',hx,hv.eventually (eventually_lt_nhds (show (0:ℝ)< 1/128 from by norm_num))] with n h₁ h₂ hu P hP; subst n; exact ⟨⟨ha,h₁,h₂⟩,hu⟩
noncomputable def bigF (Z:Fees):= max Z.bc Z.bf
lemma awards (b:ℝ)(h:0≤b) :∃ u:ℝ, 0 < u ∧ Geneva.Kappa m u (1024*b)<1:=by
    let B:=1+ ((m+1:ℕ):ℝ) * (2048*b); have hB:0 <B:=by unfold B; positivity
    refine ⟨(1/2)/B,(by positivity),?_ ⟩
    have ht:B*((1/2)/B)=1/2:=(by field_simp)
    unfold Geneva.Kappa; rw [show (1/2)/B+_=B*((1/2)/B) from (by unfold B; ring),ht]; norm_num
-- choose before-cost ceiling after K.C.L
variable (K:MapPrices)
structure Prepared (K:MapPrices)(i:ℕ)(L:Side)(G:Gauge) :Prop where
    pre : Alto.BeforeL i L K G
    buy (P:Patch)(h:P.L=L)(s p j:ℕ) : s ≤ i → p ≤ i → j ≤ i → ∃ u:ℝ, let V:=seats K i j s; mortgage (stamping V s) P p u∧Geneva.Kappa p u (1024*bigF V)<1
lemma furnish: ∀ᶠ n:ℕ in atTop,∀ L:Side,n=L.val→Prepared K i L G:=by
   have he(s p j:ℕ):∀ᶠ n:ℕ in atTop,∀ P:Patch,P.L.val=n →∃ u:ℝ,let Z:=seats K i j s; mortgage (stamping Z s) P p u ∧Geneva.Kappa p u (1024*bigF Z)<1:=by
        let Z:=seats K i j s; obtain ⟨u,hv,hK⟩:= awards p (bigF Z) ((moneyN K j s).trans (le_max_left ..)); exact (heightsP p (stamping Z s) u hv).mono fun n h P hm=> ⟨u,h _ hm,hK⟩
   let b:= Finset.range (i+1); filter_upwards [ceremony K G i,b.eventually_all.mpr (fun s _=> b.eventually_all.mpr fun p _=> b.eventually_all.mpr fun k _=>he s p k)] with n he hv g hg; subst n; exact ⟨he g rfl,fun P h s p k hs hp hk=>hv s (mem_range.mpr (by omega)) p (mem_range.mpr (by omega)) k (mem_range.mpr (by omega)) P (congr_arg (fun i:Side=>i.val) h)⟩
lemma paymentP : ∃ v:ℕ→ℕ,∀ i:ℕ,∀ g:Side,v i ≤ g.val→Prepared K i g G:=by choose v hv using fun i=>eventually_atTop.mp (furnish i K (G:=G)); exact ⟨v, fun i g he=>hv i g.val he g rfl ⟩
end YM.MSbar.Ballet
