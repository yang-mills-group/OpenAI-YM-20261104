import YM.SchemeConversionRG11.FirstW.Ship.Weight
/-! Bound local multilinear stencils using arbitrary discrete rate per oriented anchor. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T : Itinerary} {G : Gauge} {X : Type*}
def plume (T : Itinerary) (x : StepPath T) (s : Cover) (i) (b : Axis) : Edge (Site (T.period i)) := (x i + wrap (T.period i) s,b)
-- local support fixed in native units behind possibly moving test
abbrev Sight (T : Itinerary) (G : Gauge) := ∀ i, FullT G (T.period i)
def Gentle (T : Itinerary) (o : StepPath T) (A : Sight T G) := ∀ x:Cover, ∀ b : Axis, Dear T (fun i=> A i (plume T o x i b))
def Tip (T : Itinerary) (o : StepPath T) (A : Sight T G) := ∀ x:Cover,∀ b:Axis,Fleck T (fun i=>A i (plume T o x i b))
lemma doubles {E F D : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup D] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ D] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (B:E→ₗ[ℝ] F→ₗ[ℝ] D) : ∃ P:E→L[ℝ] F→L[ℝ] D, ∀ a b,P a b=B a b := ⟨((LinearMap.toContinuousLinearMap : (F→ₗ[ℝ] D)≃ₗ[ℝ](F→L[ℝ] D)).toLinearMap ∘ₗ B).toContinuousLinearMap,fun _ _ => rfl⟩
def clearWind (G : Gauge) (s : Finset (Edge Cover)) (u : ↥s → G.Color) : Wind G ℤ := fun i=> if h:i∈s then u ⟨i,h⟩ else 0 -- binder unused
-- local supports of cover functionals in this first-order analysis
lemma boardAt_same (x : Cover) (b : Step) (A B : Wind G ℤ) (h : A (b.used x)=B (b.used x)) : boardAt x b A=boardAt x b B := by simp only [boardAt,LinearMap.smul_apply,LinearMap.proj_apply,h]
lemma finite_ways (G : Gauge) (x : Cover) (w : Walk) : ∃ X:Finset (Edge Cover),
    (∀ A B:Wind G ℤ, EqOn A B X → rail x w A=rail x w B) ∧ ∀ A B C D: Wind G ℤ, EqOn A B X → EqOn C D X → swerve x w A C= swerve x w B D := by
  induction w generalizing x with
  | nil=> refine ⟨∅,fun A B _=>?_,fun A B C D _ _=>?_⟩; simp [rail];simp [swerve]
  | cons a w ih=>
    obtain ⟨X,hX,H⟩:=ih (x+a.vec); refine ⟨insert (a.used x) X, fun A B he=>?_,fun A B C D he hp=>?_⟩
    · rw [rail,LinearMap.add_apply,LinearMap.add_apply,hX A B (he.mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))),boardAt_same _ _ A B (he (Finset.mem_insert_self ..))]
    have hu : ↑X ⊆ (↑(insert (a.used x) X):Set (Edge Cover)) := Finset.coe_subset.mpr (Finset.subset_insert _ _)
    rw [swerve_eq,swerve_eq,boardAt_same _ _ A B (he (Finset.mem_insert_self ..)),hX C D (hp.mono hu), H A B C D (he.mono hu) (hp.mono hu)]
lemma finite_glow (k : Labels.Key G) : ∃ X:Finset (Edge Cover),
    ∀ A B C D: Wind G ℤ, EqOn A B X→ EqOn C D X → echoAt 0 k A C=echoAt 0 k B D := by
  choose X hX HX using fun i a (p:Fin k.1→Axis) (u:Finset (Fin k.1))=> finite_ways G 0 (patch (Bare.walk p u) i a)
  let S:= Finset.univ.biUnion fun i:Axis=> Finset.univ.biUnion fun a:Axis=> Finset.univ.biUnion fun p:Fin k.1→Axis=> Finset.univ.biUnion fun u:Finset (Fin k.1)=> X i a p u
  have hS (i a:Axis) (p:Fin k.1→Axis) (u:Finset (Fin k.1)) : ↑(X i a p u) ⊆ (↑S:Set (Edge Cover)) := fun x hx=> by simp only [S,Finset.mem_coe,Finset.mem_biUnion]; exact ⟨i,Finset.mem_univ _,a,Finset.mem_univ _,p,Finset.mem_univ _,u, Finset.mem_univ _,hx⟩
  let f (s:Signed) := fun l : Edge Cover=> ((posDir l.2).rotate s).used (s.act l.1)
  let Y:= Finset.univ.biUnion fun s=> S.image (f s)
  have he (A B:Wind G ℤ)(h:EqOn A B ↑Y) s : EqOn (Bare.wideLink G s A) (Bare.wideLink G s B) ↑S := by intro l hl; simp only [Bare.wideLink_apply]; rw [show _=_ from h (x:=f s l) (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,Finset.mem_image_of_mem (f s) hl⟩)] -- x binder
  have hv(A B C D:Wind G ℤ)(ha:EqOn A B ↑Y) (hb:EqOn C D ↑Y) : sheer G k.1 0 A C= sheer G k.1 0 B D := by
    simp only [sheer_eq,Signed.act_zero,affine,add_zero]; refine congrArg _ (Finset.sum_congr rfl (fun s _=>?_)); apply congrArg _; apply congrArg _; funext i a p; simp only [rush,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.pi_apply,LinearMap.smul_apply,LinearMap.sum_apply]
    apply congrArg _; refine Finset.sum_congr rfl (fun j hj=>?_); rw [HX i a p j _ _ _ _ ((he A B ha s).mono (hS i a p j)) ((he C D hb s).mono (hS i a p j))]
  exact ⟨Y,fun A B C D ha hb=> by simp only [echoAt,LinearMap.compr₂_apply,glint_once]; rw [hv A B C D ha hb,hv C D A B hb ha]⟩
-- evaluate fin-support projected variation
variable {o : StepPath T} {A B : Sight T G}
def cle (G : Gauge) (s : Finset (Edge Cover)) : (s→G.Color)→ₗ[ℝ] Wind G ℤ where
  toFun := clearWind G s
  map_add' x y:= by ext1 j; dsimp only [clearWind,Pi.add_apply]; split <;> simp
  map_smul' c x:= by ext1 j; dsimp only [clearWind,Pi.smul_apply,RingHom.id_apply]; split <;> simp
lemma pays_tip (hA : Tip T o A) (hB : Gentle T o B) (k : Labels.Key G) : Fleck T (fun i=>echoAt (o i) k (A i) (B i)) := by
  obtain ⟨s,H⟩ := finite_glow k
  let LeanA (A : Sight T G) (i : ℕ) (a : ↥s) := terms (o i) (A i) a.val
  have he (A : Sight T G) (i) (a : ↥s) : LeanA A i a = A i (plume T o a.val.1 i a.val.2) := by simp only [LeanA,terms,LinearMap.pi_apply,LinearMap.proj_apply,plume,add_comm]
  have hi : Fleck T (LeanA A) := fun k=> by rw [tendsto_pi_nhds]; intro a; simp only [Pi.smul_apply, Pi.zero_apply]; change Tendsto (fun j=>(T.gap j^k)⁻¹ • LeanA A j a) atTop (𝓝 0);simp only [he]; exact hA _ _ k
  -- Dear via rate maximum
  choose J hJ using fun a:↥s=> (hB a.val.1 a.val.2)
  let Z:=Finset.univ.sup J
  have hp : Dear T (LeanA B) := by
    refine ⟨Z,tendsto_pi_nhds.mpr fun i=>?_⟩; simp only [Pi.smul_apply,Pi.zero_apply]; change Tendsto (fun j=>T.gap j ^ Z • LeanA B j i) atTop (𝓝 0); simp only [he]; exact Dear.raise (hJ i) (Finset.le_sup (s:=Finset.univ) (Finset.mem_univ i))
  obtain ⟨P,ht⟩ := doubles (((echoAt (0:Cover) k).compl₂ (cle G s)).comp (cle G s))
  have hz (B:Sight T G) (i:ℕ): EqOn (cle G s (LeanA B i)) (terms (o i) (B i)) ↑s := fun a ha=>by dsimp [cle,LeanA,clearWind]; first | rw [dif_pos (show a∈s from ha)] | rw [if_pos (show a∈s from ha)]
  have hh (i : ℕ) : P (LeanA A i) (LeanA B i) = echoAt (o i) k (A i) (B i) := by rw [ht,LinearMap.comp_apply,LinearMap.compl₂_apply, H _ (terms (o i) (A i)) _ (terms (o i) (B i)) (hz _ i) (hz _ i),echo_wrap, map_zero,zero_add]
  simp_rw [←hh]; exact hi.with hp P
end YM.RG11.FirstW
