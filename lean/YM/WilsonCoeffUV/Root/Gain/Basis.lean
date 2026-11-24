import YM.WilsonCoeffUV.Root.Gain.Tests
/-! Fixed taps. No canonical moment path asked from ward consumer.
Use finite position basis; NO replacement in physical label definition. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X Z D':ℝ}
section
variable {E:Type*}[AddCommGroup E][Module ℝ E] {T:Submodule ℝ (V→E)}
private def blind (T:Submodule ℝ (V→E))(S:Finset V): T→ₗ[ℝ](S→E) where
   toFun f z:= f.val z.val
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
lemma probes [FiniteDimensional ℝ T]: ∃ S:Finset V,∀ f: T,(∀ x∈ S,f.val x=0) → f=0:=by
   classical
   let K (s:Finset V):= LinearMap.ker (blind T s)
   let A (i:ℕ): Prop:= ∃ s:Finset V,Module.finrank ℝ (K s)=i
   have hx : ∃ i,A i:=⟨_,(∅:Finset V),rfl⟩
   obtain ⟨S,hS⟩:= Nat.find_spec hx
   refine ⟨S,fun f e=>?_⟩; apply Subtype.ext; funext x; let s:= insert x S
   have he : K s ≤ K S:= by
      intro p h; change (blind T s) p=0 at h; change (blind T S) p=0; exact funext fun z=> congr_fun h (⟨z.val,Finset.mem_insert_of_mem z.property⟩:s)
   have hf : K S ≤ K s:=by
      by_contra hh
      have hu:= Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge he hh); rw [hS] at hu; exact Nat.find_min hx hu ⟨s,rfl⟩
   have hb : f∈K S:= (show (blind T S) f=0 from funext fun z=> e _ z.property)
   exact congr_fun (show (blind T s) f=0 from hf hb) ⟨x,Finset.mem_insert_self ..⟩
end
lemma band_dims {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](n:ℕ): FiniteDimensional ℝ (rangeLt E n):= by
   induction n with
   | zero=> simp only [rangeLt]; infer_instance
   | succ i hi=>
     haveI : FiniteDimensional ℝ (exactDegree E i):= by unfold exactDegree; infer_instance
     rw [rangeLt_succ]; infer_instance

abbrev Jury (G:Gauge)(k:ℕ):= ↥(rangeLt (Axis→G.Color) k)
instance (G:Gauge)(k:ℕ): FiniteDimensional ℝ (Jury G k):= band_dims _
private lemma stall (G:Gauge)(k:ℕ): ∃ S:Finset E4,∀ f:Jury G k,(∀ x∈ S,f.val x=0) → f=0:=probes

def Zest (G:Gauge)(k:ℕ):= (stall G k).choose
def slideRank (k:ℕ)(p:Place.Potential G):= ‖(fun x:Zest G k=> p x.val)‖
lemma slidek (k:ℕ)(p:Place.Potential G){M:ℝ}(h:0≤M)(x:∀ i∈ Zest G k, ‖p i‖ ≤ M): slideRank k p ≤ M:=
    (pi_norm_le_iff_of_nonneg h).mpr (fun i=> x i.val i.property)
lemma slide_nn (k:ℕ)(p:Place.Potential G): 0≤ slideRank k p:=norm_nonneg (fun x: Zest G k=>p x.val)
lemma cog (G:Gauge)(k:ℕ): ∃ C:ℝ,0 ≤ C∧∀ p:Jury G k, ‖(Module.finBasis ℝ (Jury G k)).equivFun p‖ ≤ C*slideRank k p.val:=by
   let T:= rangeLt (Axis→G.Color) k
   apply charged (blind T (Zest G k)) (Module.finBasis ℝ (Jury G k)).equivFun.toLinearMap
   intro p hp; have hv (x) (hx:x∈Zest G k): p.val x=0:= congr_fun hp ⟨x,hx⟩; rw [(stall ..).choose_spec p hv,map_zero]

-- Wages enough to elicit finitely many exact polynomial taps on future side.
variable [NormedAddCommGroup V][NormedSpace ℝ V]
lemma graded {P:ChamberTen G V r} (f:Fin r→Leg G)(g:Fin r→ ℝ): pluck P (fun i=>g i • f i)=(∏ i,g i) • pluck P f:=by
   unfold pluck; rw [←tsum_const_smul'']; apply tsum_congr; intro y; rw [pressOn,pressOn]; simp only [Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,mul_smul]
variable [CompleteSpace V]
lemma gathers {α: Fin r→Type*}[∀ i,Fintype (α i)](P:ChamberTen G V r)(f: (i:Fin r)→α i→Leg G)(h: ∀ i j,Wages (f i j))(p: Twig 0 s A P)(q:0<s):
     pluck P (fun i=>∑ j,f i j)= ∑ b:(i:Fin r)→α i, pluck P (fun i=> f i (b i)):=by
   classical
   unfold pluck; rw [← Summable.tsum_finsetSum (fun b _=> (pluck_profit p q (fun i=> h i (b i))).of_norm)]; apply tsum_congr; intro y; unfold pressOn; simp_rw [Finset.sum_apply]; rw [Fintype.prod_sum (fun i j=> f i j (y i)), Finset.sum_smul]
-- combine with laurels
lemma laurels (H:Hol G)(F:Labels.Frame G h)(v:Fin r→ℕ)(W:Multiset Axis)(hk:(∑ i,v i)+W.card≤k)(p:k≤h)(D:ℕ)(ha:0<s): ∃ C:ℝ, 0≤C∧∀ (P:ChamberTen G (Vote D) r)(A M:ℝ), Twig 0 s A P→ mural P→Smooth P→ Hears F k M P→Wing 0 s M P→ ∀(f: Fin r→ Place.Potential G), (∀ i,f i∈ rangeLt _ (v i))→
    ‖pluck P (assay ∘ f) (wallope W D)‖ ≤ C*M*(∏ i,slideRank (v i) (f i)):=by
   let B i:= Module.finBasis ℝ (Jury G (v i)); let Y (i):= Fin (Module.finrank ℝ (Jury G (v i)))
   let V i (j:Y i):= (B i j).val
   have hv (i j): V i j∈ rangeLt (Axis→G.Color) (v i):= (B i j).property
   choose C hc hx using fun b : (i:Fin r)→ Y i=> suture F H (fun i=> V i (b i)) v W (fun i=> hv i (b i)) hk p D ha
   choose T ht H' using fun i=> cog G (v i)
   refine ⟨∑ b,(∏ i,T i)*C b,Finset.sum_nonneg (fun i _=> mul_nonneg (Finset.prod_nonneg fun _ _=> ht _) (hc _)),fun P A M q u e z a f g=> ?_⟩
   let d:=wallope W D; let x i: Jury G (v i):= ⟨f i,g i⟩; let c (i):= (B i).equivFun (x i)
   let Q i (j:Y i):= c i j • assay (V i j)
   have hq i j: Wages (Q i j):= pays_assay _ (Submodule.smul_mem (rangeLt _ (v i)) (c i j) (hv i j))
   have he i: assay (f i) = ∑ j,Q i j:=by
       let L: Jury G (v i)→ₗ[ℝ] Leg G := {
           toFun z:= assay z.val
           map_add' _ _:=rfl
           map_smul' _ _:= rfl }
       change L (x i)=_; conv_lhs=>rw [← (B i).sum_repr (x i),map_sum]
       apply Finset.sum_congr rfl; intro j _; rw [map_smul]; rfl
   have hg i j : ‖c i j‖≤ T i*slideRank (v i) (f i):= le_trans (norm_le_pi_norm (c i) j) (H' i _)
   rw [show assay∘f=fun i=>∑ j,Q i j from funext he,gathers P Q hq q ha,_root_.sum_apply]; simp_rw [Finset.sum_mul]
   refine le_trans (norm_sum_le ..) (Finset.sum_le_sum (fun b _=>?_)); unfold Q; rw [graded,_root_.smul_apply,norm_smul];
   rw [norm_prod]; refine (mul_le_mul (Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> hg i _)) (hx b P A M q u e z a) (norm_nonneg _) (Finset.prod_nonneg (fun i _=> mul_nonneg (ht _) (slide_nn ..)))).trans_eq ?_; rw [Finset.prod_mul_distrib]; ring
end YM.WilsonCoeffUV.Cosmos
