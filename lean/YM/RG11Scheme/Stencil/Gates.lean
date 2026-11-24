import YM.RG11Scheme.Stencil.Detector

/-! The collapse on two legs of ONE mark, including the internal first completion at that mark. This unsubtracted cover current is horizontal already on compact lattice gradients. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 54000
set_option maxRecDepth 8000
noncomputable section
namespace YM.RG11Scheme.Stencil.Cell
open Filter Function Set Lattice Mesh Pert Pert.First Spark Bare
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G:Gauge}{X I : Type} [Fintype I] {D E F:Type*} {j k : ℕ}
abbrev Scalar (G:Gauge) (j:ℕ) := Module.Dual ℝ (Labels.Taylor G j)
def forward (v:Scalar G j) (x:Cover) (h:ℝ) : Dual G := v ∘ₗ wideLinear G j h x
def cross (v:Scalar G j) (x:Cover) (h:ℝ) : Bond G →ₗ[ℝ] Bond G→ₗ[ℝ] ℝ := (full2 h x j).compr₂ v
lemma forward_div (v:Scalar G j)(x:Cover)(h) : horizontal (forward v x h) := by 
    intro ε; rw [forward, LinearMap.comp_apply,show gradient ε=tremor ε from rfl, shadow,map_zero]
lemma cross_ward (v:Scalar G j)(x:Cover)(h) (A:Bond G)(ε:Cover→G.Color) : cross v x h A (gradient ε)+forward v x h (arc ε A) = forward v x h (point_ad (ε x) A) := by 
    rw [show gradient ε=tremor ε from rfl, show point_ad (ε x) A= indye (ε x) A from funext fun _=>rfl]; unfold cross forward
    simp only [LinearMap.compr₂_apply,LinearMap.comp_apply]
    rw [←v.map_add, sunlight]
lemma finite_assembly (f:I→(X→E)→F) (hf:∀ i,brief (f i)) : brief fun x i=>f i x := ⟨Finset.univ.biUnion (fun i=>(hf i).choose),fun a b he=>funext fun i=> (hf i).choose_spec a b (fun l hl=> he l (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,hl⟩))⟩
lemma sew (f:I→(X→E)→F)[AddCommMonoid F] (hf:∀ i,brief (f i)) : brief fun x=>∑ i,f i x := (finite_assembly f hf).then (fun a:I→F=> Finset.sum Finset.univ a)
lemma joins {U : Type} (f:X→(U→E)→F) (g:(X→F)→D) (h:∀ i,brief (f i)) (hh:brief g): brief fun x=>g (fun i=>f i x) := ⟨hh.choose.biUnion (fun i=>(h i).choose),fun _ _ e=>hh.choose_spec _ _ (fun i hi=>(h i).choose_spec _ _ (fun l hl=> e l (Finset.mem_biUnion.mpr ⟨i,hi,hl⟩)))⟩

local notation "Δ" => Bond G
private lemma face_brief (x:Cover)(i k:Axis) : brief fun U:Δ=>wideCurl U x i k := (((brief.one (x,i)).combine (brief.one (x+step i,k)) ((· + ·) : G.Color → G.Color → G.Color)).combine (brief.one (x,k)) (· - ·)).combine (brief.one (x+step k,i)) (· - ·)
private lemma core_brief (v:Cover)(j:ℕ) : brief fun U:Δ=> wideCore G j v U := by
   apply finite_assembly (fun i (U:Δ) => wideCore G j v U i); intro i
   apply finite_assembly (fun k (U:Δ) => wideCore G j v U i k); intro k
   apply finite_assembly (fun (γ:Fin j→Axis) (U:Δ) => wideCore G j v U i k γ); intro γ
   simp_rw [wideCore_apply]; exact (sew _ (fun s=> (face_brief (G:=G) (v+∑ i∈s,step (γ i)) i k).then (Bare.sign s • ·))).then (((j.factorial:ℝ)⁻¹) • ·)
private lemma wide_brief (s:Signed)(l) : brief fun U:Δ=>wideLink G s U l := by simp_rw [wideLink_apply]; exact (brief.one (((posDir l.2).rotate s).used (s.act l.1))).then ((if ((posDir l.2).rotate s).neg then -1 else (1:ℝ)) • ·)
lemma lend (h:ℝ)(v:Scalar G j) (x:Cover) : brief (forward v x h) := by
    have hb (s:Signed): brief (fun U:Δ=> wideCore G j (affine s⁻¹ 0 x) (wideLink G s U)) := joins (fun l (U:Δ)=>wideLink G s U l) (fun B:Δ=>wideCore G j (affine s⁻¹ 0 x) B) (wide_brief s) (core_brief _ _)
    have hg (s:Signed) := (hb s).then (F:=Response G j) (Y:=Labels.Taylor G j) (outside h s j)
    simp only [forward,LinearMap.coe_comp,Function.comp_def,sided]
    with_reducible exact (brief.then (F:=Labels.Taylor G j) (Y:=ℝ) (sew _ hg) (fun u=> v ((Fintype.card Signed:ℝ)⁻¹ • u)))
lemma arc_compact (A : Bond G){ε:Cover→G.Color} (hp:ε.HasFiniteSupport) : (arc ε A).HasFiniteSupport := product_finite _ (fun i=> (show (support ε ∪ support (fun x => ε (x+step i))).Finite from hp.union (plus_compact hp)).subset (fun x hx=>by contrapose! hx; simp at hx; simp [arc,hx]))

def collapse (p:Scalar G j) (q:Scalar G k)(x:Cover)(h:ℝ)(A:Bond G):ℝ :=
   let L:= forward p x h
   let M:= forward q x h
   cross p x h (ray M) A+cross q x h (ray L) A- ∑' z:Cover,surge (ray L) (ray M) A z
theorem surplus {L M:Dual G}(h:horizontal L)(hh:horizontal M)(q:brief L)(r:brief M){ε:Cover→G.Color}(p:ε.HasFiniteSupport) : (∑' z:Cover,surge (ray L) (ray M) (gradient ε) z)= -(L (arc ε (ray M))+M (arc ε (ray L))) := by
   have he:=arc_compact (ray L) p
   have hf:=arc_compact (ray M) p
   simp_rw [third_ward, tsum_neg, Summable.tsum_add (summable_of_hasFiniteSupport (variational_finite (A:=ray L) hf)) (summable_of_hasFiniteSupport (variational_finite (A:=ray M) he)), collects h q hf, collects hh r he]
lemma invisible (p:Scalar G j) (q:Scalar G k) (h x) {ε:Cover→G.Color}(hp:ε.HasFiniteSupport) : collapse p q x h (gradient ε)=0 := by
   simp only [collapse]
   rw [surplus (forward_div p x h) (forward_div q x h) (lend h p x) (lend h q x) hp]
   let L:=forward p x h
   let M:=forward q x h
   have he:=cross_ward p x h (ray M) ε
   have hv:=cross_ward q x h (ray L) ε
   have hh:=rotation_sum L M (lend h p x) (lend h q x) (ε x)
   dsimp only [L,M] at he hv hh
   with_reducible apply bridge_values he hv hh
where
 bridge_values {a b l m c d:ℝ} (h:a+l=c) (p:b+m=d) (e:c+d=0): a+b- -(l+m)=0:= by linarith
end YM.RG11Scheme.Stencil.Cell
