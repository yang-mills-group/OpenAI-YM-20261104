import YM.OPE.Levy.Transit
/-! Procure actual path with extra station prices on ALL sublimits.
Adapted from :: UVStress.Station.harvested and UVStress.Stations.ranging;
hierarchy agreement for the very same same sublimits, no composite indices
between physical cutoff and the UV measurement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Next.UVStress
open Bid Dash Next.Extract Push.RelayDifference Spec
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G}{F : Order} {T' R}{A S : Table C.book} {V W:DiffPlan S}
   (L:Base C F A T' R S V) (hu: W.Inclusions S) (hg:G.Simple) (hQ:RoughFactory C) (h:Stocked C F){D:ℕ}(hO:F.Ordered C S)(hPt:F.PointLimits C S)
local notation "T₀" => (Bel C.book)
-- Fresh choices at FIXED depth station only for reading the physical ordered quotient
-- `U.r` will pass to the path only later.
def Fitted (F:Order) (X:YM.Next.UVStress.Station C D)(U:Panel S) := ∃ (b:Filter Cutoffs)(_ : b.NeBot), b ≤ F.fuse ∧ ∀ (d:Fin (D+1)) u,∃ x,
  Tendsto (fun i=>X.atCut i d u) b (𝓝 x) ∧ U d u=S.project ↑d x
lemma harvested (H : S.Hierarchy) (h : F.Ordered C S) (a : (Bel C.book).RealSpin)
    (X : YM.Next.UVStress.Station C D) {N : ℕ} {R ε : ℝ} (hs : X.Admissible F a N R ε) :
    ∃ U : Panel S,
      (∀ d≤D, StraightAt H.spin a U d) ∧ U 0 ((Bel C.book).unit 0)=S.unit 0 ∧
      Fitted F X U ∧ (∀ (n : ℕ), n ≤ N → ∀ v : Fin n → (Bel C.book).Tag, (∀ i,(v i).1 ≤ D) →
        ∀ t : Test n, tsupport t ⊆ Scaling.window R n →
        ∀ M : ℝ, 0 < M → (∀ x, ‖t x‖ ≤ M) →
        ‖t.applyTo (tested X.r U v) - t.applyTo (disc v)‖ ≤ ε * YM.Next.UVStress.Station.charge v * M) := by
  obtain ⟨A,hA⟩ := hs.lift_bound
  obtain ⟨b,hb,hU,Y,hY⟩ := finite_extract (𝓛:=F.fuse) X.atCut A hA
  have he i (x) : Tendsto (fun j => X.atCut j i x) b (𝓝 (Y i x)) :=
    Dash.arcing (tendsto_pi_nhds.mp hY i) tendsto_const_nhds
  let U (d : ℕ) : (Bel C.book).Field d →ₗ[ℂ] S.Field d :=
    if h : d≤D then (S.project d).comp (Y (⟨d,Nat.lt_succ_of_le h⟩ : Fin (D+1))).toLinearMap else 0
  have eq (d : ℕ) (h : d≤D) x : U d x=S.project d (Y ⟨d,Nat.lt_succ_of_le h⟩ x) := by simp only [U,dif_pos h]; rfl
  let z : Fin (D+1) := ⟨0,Nat.succ_pos _⟩
  refine ⟨U,fun d hd => ?_, ?_,?_, fun n hn v hv t ht M hm ht' => ?_⟩
  · let i : Fin (D+1) := ⟨d,Nat.lt_succ_of_le hd⟩
    constructor
    · intro x; rw [eq d hd,eq d hd,S.conj_project]; apply congr_arg
      exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).conj a d x)) (he i x).star
        (((show ∀ᶠ j in F.fuse, ∀ (i : Fin (D+1)) v, X.atCut j i ((Bel C.book).conj a i v) = star (X.atCut j i v) from hs.lift_real)).filter_mono hb |>.mono fun _ h => h i x)
    intro s x; rw [eq d hd,eq d hd,S.mirror_project]; apply congr_arg
    exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).mirror a d s x))
      ((C.book.mirrorGroup d s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (he i x))
      (((show ∀ᶠ j in F.fuse, ∀ (i : Fin (D+1)) s v, X.atCut j i ((Bel C.book).mirror a i s v) = C.book.mirrorGroup i s (X.atCut j i v) from hs.lift_signed)).filter_mono hb |>.mono fun _ h => h i s x)
  · rw [eq _ (Nat.zero_le _)]
    apply congr_arg (S.project 0)
    refine tendsto_nhds_unique_of_eventuallyEq (he z ((Bel C.book).unit 0)) tendsto_const_nhds ?_
    exact (show ∀ᶠ u in F.fuse, X.atCut u z ((Bel C.book).unit 0) = C.book.scalar 0 from hs.lift_unit).filter_mono hb
  · exact ⟨b,hU,hb,fun d x=>⟨Y d x,he _ _,eq d (Nat.le_of_lt_succ d.isLt) x⟩⟩
  let g : Caps n := fun i => (v i).1
  let m (j) (i : Fin n) : C.book.Ref (g i) := X.atCut j ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  let y (i : Fin n) : C.book.Ref (g i) := Y ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  have hh : S.integralOn g y (dilate X.rad t)=t.applyTo (tested X.r U v) := by
    unfold Table.integralOn; rw [zoom_integral]
    apply t.apply_eq; intro x hx
    change S.value g _ y = S.useAt S _ (panels U ∘ v)
    let l : Fin n → C.book.Token := fun i => ⟨g i,y i⟩
    rw [show panels U ∘ v = S.classTokens ∘ l from funext (fun i => by
      unfold panels Function.comp
      change Sigma.mk (g i) (U (g i) ((v i).2)) = Sigma.mk (g i) (S.project (g i) (y i))
      rw [eq _ (hv i)])]
    exact (S.at_project S H.laws.toSymmetric (fun _ => le_rfl) ((enlarged X.rad _).1 hx) l).symm
  have hz : Tendsto (fun j : ℕ×ℕ => X.paid v hv t j.1 j.2) b (𝓝 (t.applyTo (tested X.r U v))) := hh ▸
    calibrated_smear h b hb _ (v:=m) (x:=y) fun i => he ⟨(v i).1,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  refine le_of_forall_pos_le_add fun η hη => ?_
  exact le_of_tendsto ((hz.sub_const (t.applyTo (disc v))).norm)
    ((show ∀ᶠ i in F.fuse, ‖X.paid v hv t i.1 i.2 - t.applyTo (disc v)‖ ≤ ε * YM.Next.UVStress.Station.charge v * M + η from
      hs.short hn v hv t ht M hm ht' η hη).filter_mono hb)

include h L hQ hu hg hO hPt
lemma prod_demand (hB:(T₀).Smooth)(a:(T₀).RealSpin) (m n:ℕ)(R ε δ:ℝ)(hr:1 ≤ R)(he:0<ε)(hd:0<δ):∃ X:YM.Next.UVStress.Station C m,X.Admissible F a n R ε ∧ X.r ≤ δ ∧ (∀ d e, weightFit F W X d e (Real.exp ((ε-e.val)*(-Real.log X.r)))):=by
   obtain ⟨w,hw,h'⟩:= h n m R hB a (zero_lt_one.trans_le hr)
   obtain ⟨z,ψ,D,K⟩:=hQ
   obtain ⟨i, hv,hd,hy⟩:= ((supply_wheel w hw hO L.clean.smooth L.family hPt hB (zero_lt_one.trans_le hr) ε he).and ((hw.small.eventually (ge_mem_nhds hd)).and
     (eventually_all.mpr fun d=>eventually_all.mpr fun e=>impact K L hu hg h' d e ε he))).exists
   exact ⟨(w i).toStation, hv,hd,hy⟩

lemma ranging_supply (hB:(T₀).Smooth)(a:(T₀).RealSpin):
    ∃ (R : Zoom) (X : (k : ℕ) → YM.Next.UVStress.Station C k),
      ∀ k, (X k).r=R.r k ∧ (X k).Admissible F a k (sizeHint k) (costHint k) ∧
        (∀ d e, weightFit F W (X k) d e (Real.exp ((costHint k-e.val)*(-Real.log (R.r k))))) := by
  have hv k δ (hd : 0<δ) := prod_demand L hu hg hQ h hO hPt hB a k k (sizeHint k) (costHint k) δ (by unfold sizeHint; simp) (cost_pos _) hd
  let Good (k : ℕ) := {X : YM.Next.UVStress.Station C k // X.Admissible F a k (sizeHint k) (costHint k) ∧ X.r ≤ costHint k ∧ (∀ d e, weightFit F W X d e (Real.exp ((costHint k-e.val)*(-Real.log X.r))))}
  let b : Good 0 := ⟨(hv 0 (costHint 0) (cost_pos _)).choose,(hv 0 _ (cost_pos _)).choose_spec⟩
  have he (k : ℕ) (X : Good k) : ∃ y : Good (k+1), y.val.r < X.val.r := by
    obtain ⟨Y,hY,H,hh⟩ := hv (k+1) (min (X.val.r/2) (costHint _)) (lt_min (half_pos X.val.rad) (cost_pos _))
    exact ⟨⟨Y,hY,H.trans (min_le_right ..),hh⟩,(H.trans (min_le_left ..)).trans_lt (half_lt_self X.val.rad)⟩
  let p (k : ℕ) : Good k := Nat.rec b (fun k x => (he k x).choose) k
  have h (k : ℕ) : (p (k+1)).val.r < (p k).val.r := (he k (p k)).choose_spec
  refine ⟨⟨fun k => (p k).val.r,fun k => (p k).val.rad,strictAnti_nat_of_succ_lt h,?_⟩,
    fun k => (p k).val,fun k => ⟨rfl,(p k).property.1,(p k).property.2.2⟩⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun k => (p k).val.rad.le)
    (fun k => (p k).property.2.1)


end YM.OPE.Levy
