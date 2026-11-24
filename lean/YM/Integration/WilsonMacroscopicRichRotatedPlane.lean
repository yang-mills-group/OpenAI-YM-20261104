import YM.Integration.WilsonMacroscopicRichMovingPlane
import YM.Work.A01.Mirror

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichRotatedPlane
open YM YM.Spec YM.PhysMS YM.Trace.Pilot YM.Table.Pairing YM.Spin YM.Climb YM.Next.UVStress YM.Work.A01
open Filter Set WilsonMacroscopicRichReflectedRoster WilsonMacroscopicRichMovingPlane
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

private lemma first {n m:ℕ}(r τ:ℝ)(x:Points n)(y:Points m)(i:Fin n):placed r τ x y (Fin.castAdd m i)=r•x i:=Fin.append_left (fun i=>r•x i) (fun j=>τ•y j) i
private lemma last {n m:ℕ}(r τ:ℝ)(x:Points n)(y:Points m)(j:Fin m):placed r τ x y (Fin.natAdd n j)=τ•y j:=Fin.append_right (fun i=>r•x i) (fun j=>τ•y j) j
private lemma move {n m:ℕ}(s:Ortho)(r τ:ℝ)(x:Points n)(y:Points m):
    Points.move s (placed r τ x y)=placed r τ (Points.move s x) (Points.move s y):=by
  apply PiLp.ext;intro k;refine Fin.addCases ?_ ?_ k
  · intro i;rw [Points.move_coord,first,first,Points.move_coord];exact s.motion.map_smul r (x i)
  · intro i;rw [Points.move_coord,last,last,Points.move_coord];exact s.motion.map_smul τ (y i)

private lemma continuousMove {n:ℕ}(s:Ortho):Continuous (Points.move (n:=n) s):=by
  apply (PiLp.continuous_toLp _ _).comp;apply continuous_pi;intro i
  exact s.motion.continuous.comp ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>E4)).continuous)

/-- A fixed signed orientation covers an entire compact angular sector of the physical exterior.
The aperture relative to its scale is selected before the two independent physical running radii. -/
theorem original (F:Spec.Final C f S)(J:ℝ→tower S)(H:Leading F J){n m:ℕ}(s:Signed)(a:Axis)(δ:ℝ)(positive:0<δ)
    (K:Set (Points n))(L:Set (Points m))(hK:IsCompact K)(hL:IsCompact L)(xSafe:K⊆conf n)(ySafe:L⊆conf m)
    (side:∀y∈L,∀j,δ≤(s.ortho.motion (y j)) a)(v:Fin n→(Bel C.book).Tag)(w:Fin m→(Bel C.book).Tag):
    ∃η:ℝ,0<η ∧ ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,r/τ≤η → ∀x∈K,∀y∈L,
      ‖S.useAt S (placed r τ x y) (Fin.append (fun i=>physical J r (v i)) (fun j=>physical J τ (w j)))‖≤B:=by
  obtain ⟨M,hM⟩:=hK.exists_bound_of_continuousOn (f:=fun x:Points n=>x) continuousOn_id
  let A:=max 0 M+1
  have hA:0<A:=by dsimp [A];positivity
  let c:E4:=WithLp.toLp 2 (fun _:Axis=>A)
  let η:=δ/(2*A)
  have he:0<η:=div_pos positive (by positivity)
  let K':=Points.move s.ortho '' K;let L':=Points.move s.ortho '' L
  have kIn:K'⊆conf n:=by rintro _ ⟨x,hx,rfl⟩;exact Points.move_in _ (xSafe hx)
  have lIn:L'⊆conf m:=by rintro _ ⟨y,hy,rfl⟩;exact Points.move_in _ (ySafe hy)
  have near:∀x∈K',∀i,x i a<c a:=by
    rintro _ ⟨x,hx,rfl⟩ i
    change (s.ortho.motion (x i)) a<A
    have bound:|(s.ortho.motion (x i)) a|≤‖x‖:=by
      calc
        _ ≤ ‖s.ortho.motion (x i)‖ := PiLp.norm_apply_le _ _
        _ = ‖x i‖ := s.ortho.motion.norm_map _
        _ ≤ ‖x‖ := PiLp.norm_apply_le _ _
    exact (le_abs_self _).trans_lt ((bound.trans ((hM x hx).trans (le_max_right 0 M))).trans_lt (lt_add_one _))
  have far:∀y∈L',∀u∈Icc 0 η,∀j,(u•c) a<y j a:=by
    rintro _ ⟨y,hy,rfl⟩ t ht j
    change t*A < (s.ortho.motion (y j)) a
    have ar:t≤δ/(2*A):=ht.2
    have small: t*(2*A)≤δ:=(le_div_iff₀ (by positivity)).mp ar
    exact lt_of_lt_of_le (by nlinarith) (side y hy j)
  let rotate:=mirrorTag (Maxwell.Free.spin_free C.labels) s
  obtain ⟨B,hB,U,hU,bill⟩:=WilsonMacroscopicRichMovingPlane.original F J H a c η K' L'
    (hK.image (continuousMove _)) (hL.image (continuousMove _)) kIn lIn near far (rotate ∘ v) (rotate ∘ w)
  have hi:∀ᶠr in trail,∀i,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (v i).1):=Filter.eventually_all.2 (fun i=>H.equivariant (v i).1)
  have hj:∀ᶠr in trail,∀j,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (w j).1):=Filter.eventually_all.2 (fun j=>H.equivariant (w j).1)
  let V:Set ℝ:={r| r∈U ∧ 0<r ∧ (∀i,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (v i).1)) ∧
    ∀j,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (w j).1)}
  refine ⟨η,he,B,hB,V,?_,?_⟩
  · filter_upwards [hU,self_mem_nhdsWithin,hi,hj] with r u pos h k using ⟨u,pos,h,k⟩
  intro r hr τ hτ gap x hx y hy
  have x':Points.move s.ortho x∈K':=mem_image_of_mem _ hx
  have y':Points.move s.ortho y∈L':=mem_image_of_mem _ hy
  have apart:placed r τ x y∈conf (n+m):=by
    change Function.Injective (Fin.append (fun i : Fin n=>r•x i) (fun j : Fin m=>τ•y j))
    apply Fin.append_injective_iff.mpr
    refine ⟨fun i j e=>xSafe hx ((smul_right_injective _ hr.2.1.ne') e),fun i j e=>ySafe hy ((smul_right_injective _ hτ.2.1.ne') e),?_⟩
    intro i j eq
    have h1: (s.ortho.motion (x i)) a<A:=near _ x' i
    have h2: (r/τ)*A<(s.ortho.motion (y j)) a:=far _ y' _ ⟨(div_pos hr.2.1 hτ.2.1).le,gap⟩ j
    have h3:r*A<τ*((s.ortho.motion (y j)) a):=by
      have m:=mul_lt_mul_of_pos_left h2 hτ.2.1
      rwa [←mul_assoc,show τ*(r/τ)=r by field_simp [hτ.2.1.ne']] at m
    have coord:=congrArg (fun z:E4=>(s.ortho.motion z) a) eq
    change (s.ortho.motion (r•x i)) a=(s.ortho.motion (τ•y j)) a at coord
    rw [map_smul,map_smul] at coord
    exact ((mul_lt_mul_of_pos_left h1 hr.2.1).trans h3).ne coord
  let p:=Fin.append (fun i=>physical J r (v i)) (fun j=>physical J τ (w j))
  have tagged:mirrorTag F.room.kernel.spin s ∘ p=Fin.append (fun i=>physical J r (rotate (v i))) (fun j=>physical J τ (rotate (w j))):=by
    funext k;refine Fin.addCases ?_ ?_ k
    · intro i;change mirrorTag _ s (Fin.append _ _ (Fin.castAdd m i))=_;rw [Fin.append_left,Fin.append_left]
      exact congrArg (@Sigma.mk ℕ S.Field _) ((hr.2.2.1 i).1 s (v i).2).symm
    · intro j;change mirrorTag _ s (Fin.append _ _ (Fin.natAdd n j))=_;rw [Fin.append_right,Fin.append_right]
      exact congrArg (@Sigma.mk ℕ S.Field _) ((hτ.2.2.2 j).1 s (w j).2).symm
  have measured:=mirror_eval F.room.kernel.laws.toSymmetric F.room.kernel.spin apart p s
  rw [move,tagged] at measured
  exact (congrArg norm measured.symm).le.trans (bill r hr.1 τ hτ.1 gap _ x' _ y')

end YM.Integration.WilsonMacroscopicRichRotatedPlane
