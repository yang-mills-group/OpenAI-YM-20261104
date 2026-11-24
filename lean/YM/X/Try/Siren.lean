import YM.X.Try.Trench
/-!
# estimate pass X under auxiliary non-H desk. comfort high-positive six. Calibration contact-projection may drift elsewhere unbounded.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Maxwell Maxwell.Free MvPolynomial Function Set Filter MeasureTheory Asymptotics
open PertExtension LatticePT Next.Rank Next.Rank.Normal
open Pert Pert.Position Pert.RawLabels Pulse Bare Ribbon
open Interval.Size Hinge Reed Stems Haze Crate Interval
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{d k m:ℕ} {V W I:Type*} {r R:ℝ}
section alg
variable [NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V] [NormedAddCommGroup W][NormedSpace ℂ W] {R:V→L[ℂ]W} -- R notation shadow variable previous! 
lemma Op {X:ℕ→ V→L[ℂ] W} (h:∀ v:V, Tendsto (fun i=> X i v) atTop (𝓝 (R v))) : Tendsto X atTop (𝓝 R):= by
   let b:= Module.finBasis ℂ V; let I:= Fin (Module.finrank ℂ V); let u (i:I): W→L[ℂ](V→L[ℂ] W):= ContinuousLinearMap.smulRightL ℂ V W ((b.coord i).toContinuousLinearMap)
   have he (T:V→L[ℂ] W): T=∑ i:I,u i (T (b i)):= by
      ext1 x; rw [ContinuousLinearMap.sum_apply]; conv_lhs=> rw [← b.sum_repr x];
      simp_rw [map_sum,map_smul]; rfl
   refine (he R).symm ▸ Tendsto.congr ?_ (tendsto_finsetSum (a:=fun i:I=> u i (R (b i))) Finset.univ (fun i _=> (u i).continuous.continuousAt.tendsto.comp (h (b i)))); intro i; exact (he (X i)).symm
lemma Op.touch {Y:ℕ→ V→L[ℂ] W}{y:V}{p:ℕ→ V}(h:Tendsto Y atTop (𝓝 R))(he:Tendsto p atTop (𝓝 y)): Tendsto (fun k=> Y k (p k)) atTop (𝓝 (R y)):= (show Continuous (fun w: (V→L[ℂ] W) × V=> w.1 w.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds he)
lemma Op.grip {X:ℕ→V→ₗ[ℂ] W}{A:V→ₗ[ℂ] W} [FiniteDimensional ℂ W](h:∀ v,Tendsto (fun i=> X i v) atTop (𝓝 (A v)))(hp: LinearMap.ker A=⊥){f:ℕ→V}(hf:Released (fun i=> X i (f i))) : Released f:= by
    letI:= FiniteDimensional.complete ℂ V; let P:= A.leftInverse.toContinuousLinearMap; let Y(i:ℕ):= P ∘L (X i).toContinuousLinearMap; have hh : Tendsto Y atTop (𝓝 1) := by
       apply Op; intro v; have he: P (A v)=v:= LinearMap.leftInverse_apply_of_inj hp v
       have ht:= P.continuous.continuousAt.tendsto.comp (h v); rw [he] at ht; exact ht
    let Z(k:ℕ):= Ring.inverse (Y k); have hz: Tendsto Z atTop (𝓝 1):= by
       have hw:= (NormedRing.inverse_continuousAt (1 : (V→L[ℂ] V)ˣ)).tendsto; rw [Units.val_one,Ring.inverse_one] at hw; exact hw.comp hh
    obtain ⟨c,hf⟩:=hf; have hk:Tendsto (fun i=> Y i (f i)) atTop (𝓝 (P c)):= P.continuous.continuousAt.tendsto.comp hf; have ht:=Op.touch hz hk; refine ⟨_, ht.congr' ?_⟩; filter_upwards [hh.eventually (IsOpen.mem_nhds Units.isOpen (show IsUnit (1:V→L[ℂ] V) from isUnit_one))] with i hi; let t:= (f i); change ((Z i* Y i) t)= _; rw [show Z i * Y i=1 from Ring.inverse_mul_cancel _ hi]; rfl
end alg
variable {F:Labels.Frames G} (S:Bare.Shop F)(hq:1<q.val)(hg:G.Simple) (w:Floor R)(hr:R<r)
local notation "A"=> Bank F 6
local notation "T₀"=> pureBank F 6
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ℒ"=> Pert.Position.lower F 4 6
local notation "γ"=> YM.PositionX.par F 6
local notation "b₀" i=>S.bank q i 6 0
local notation "Y"=> Splot.result F
include hg in
lemma pointed : ∃(n:ℕ)(t:Fin n→ Splot F), LinearMap.ker (LinearMap.pi (fun i:Fin n=> Y (t i) T₀ ∘ₗ (halfling F).subtype))=⊥:= by
    let V:=halfling F; let Q (s:Splot F) := Y s T₀ ∘ₗ V.subtype; obtain ⟨f,hf,h,_⟩:= Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range Q); choose t ht using hf; refine ⟨_,t,le_antisymm ?_ bot_le⟩; intro x hx; apply Subtype.ext; change x.val=0; apply even_unique F hg x.val (sub_eq_zero.mp x.property); intro p
    have he: Q p∈ Submodule.span ℂ (Set.range f):=by rw [h]; exact Submodule.subset_span (Set.mem_range_self _)
    let U:= LinearMap.ker (LinearMap.applyₗ (R:=ℂ) (M₂:=ℂ) x); -- name
    have hh : Submodule.span ℂ (Set.range f)≤ U:= by refine Submodule.span_le.mpr ?_; rintro _ ⟨i,rfl⟩; rw [← ht i]; exact congr_fun (LinearMap.mem_ker.mp hx) i
    exact hh he
lemma weatherless (i:ℕ): silver F (b₀ i):= by have h:= S.bank_parity q i 6 0; simpa [silver] using h
include hq hg hr
local notation "LH" i=> Pulse.away (q:=q) (k:=i) S w 6
local notation "RH" i=> bufferL F (barter (q:=q) (k:=i) (d:=6) S w)
-- helper
abbrev width (u: Splot F) (r:ℝ):Prop:= Curve u.test⊆Pulse.Region u.n r
omit hq hg hr in
def σ (i:ℕ): Workroom F 6:= (RH i)-LH i
omit hg hr
lemma lamp (p:Splot F): Tendsto (fun i=> (Y p (b₀ i)).toContinuousLinearMap) atTop (𝓝 (Y p T₀).toContinuousLinearMap):= Op (fun x=> S.bank_white q hq (s:=Splot.sit F x p)) -- named?
omit hq in
set_option maxRecDepth 6000 in
lemma shield (p: Pert.Position.E F 6)(hp:p∈ℒ) (i:ℕ): (RH i) p∈ℒ∧ (LH i) p∈ℒ:= by exact ⟨(barter (d:=6) (q:=q) (k:=i) S w).property.2.1 _ (by omega) _ hp, stayed S w p (by omega) hp⟩ -- inspect signatures
include hg hr
lemma remit_tip (x: Pert.Position.E F 6)(hp:γ x= -x)(p:Splot F) (H:width p r) : Released (fun i=> Y p (b₀ i) ((positive F ((σ (q:=q) S w i) x)).val)):= by
    let L:= fun i:ℕ=> LH i; let M:= fun i:ℕ=> RH i; let a(i:ℕ):= remit q S M i; let b(i:ℕ):= remit q S L i
    have h₁ (a b:Bank F 6): Y p (a-b) x= Y p a x-Y p b x:= rfl
    have he(i:ℕ): Y p (b₀ i) ((positive F (σ (q:=q) S w i x)).val) = Y p (b i) x-Y p (a i) x:= by
       rw [← p.accepts F hg (weatherless ..)] -- field notation order? incorrect p first
       unfold a b remit σ; simp_rw [LinearMap.sub_apply,map_sub,h₁]; rw [p.pass_S F hg (weatherless ..) hp _ (fun v hv=> (shield (q:=q) S w v hv i).2), p.pass_S F hg (weatherless ..) hp _ (fun v hv=> (shield (q:=q) S w v hv i).1)]; ring -- notation conflict
    have hu : Released (fun i=> Y p (a i) x):= by
       let v:= (Splot.sit F x p); refine ⟨_, (inside S v.f M hq hg (fun p'=> Barter_charge S w hq p') (Barter_balance S w r hq hr) v.p H).2⟩
    have ht : Released (fun i=> Y p (b i) x):= by
       let v:= (Splot.sit F x p); exact ⟨_, (inside S v.f L hq hg (fun p'=> robust S w p' hq) (light_res S w hr hq) v.p H).2⟩
    simp_rw [he]; exact ht.sub hu
end YM.PositionX.Tri
