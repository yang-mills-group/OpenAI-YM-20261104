import YM.Integration.WilsonMacroscopicRichSeparateScales

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichMovingPlane
open YM YM.Spec YM.PhysMS YM.Trace.Pilot YM.Table.Pairing YM.Spin YM.Climb YM.Next.UVStress
open Filter Set WilsonMacroscopicRichReflectedRoster
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

def placed {n m:ℕ}(r τ:ℝ)(x:Points n)(y:Points m):Points (n+m):=
  points (Fin.append (fun i=>r•x i) (fun j=>τ•y j))

def inner {n:ℕ}(a:Axis)(c:E4)(x:Points n):Points n:=points fun i=>ride a (x i-c)
def outer {m:ℕ}(c:E4)(t:ℝ×Points m):Points m:=points fun j=>t.2 j-t.1•c

private lemma point {n:ℕ}(i:Fin n):Continuous fun x:Points n=>x i :=
  (continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>E4)).continuous

private lemma nears {n:ℕ}(a:Axis)(c:E4):Continuous (inner (n:=n) a c):=by
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi;intro i
  exact (Signed.reflect a).motion.continuous.comp ((point i).sub continuous_const)

private lemma fars {m:ℕ}(c:E4):Continuous (outer (m:=m) c):=by
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi;intro j
  exact ((point j).comp continuous_snd).sub (continuous_fst.smul continuous_const)

/-- Exact recentering in physical units, with different incoming and exterior lengths. -/
theorem location {n m:ℕ}(a:Axis)(c:E4)(r τ:ℝ)(hτ:0<τ)(x:Points n)(y:Points m):
    placed r τ x y=Points.across (r•c) (closedUp a (r•inner a c x) (τ•outer c (r/τ,y))) :=by
  apply PiLp.ext;intro k;refine Fin.addCases ?_ ?_ k
  · intro i
    change Fin.append (fun l : Fin n=>r•x l) (fun l : Fin m=>τ•y l) (Fin.castAdd m i)=_
    rw [Fin.append_left,Points.across_coord,enter]
    change r•x i = (Signed.reflect a).motion (r•ride a (x i-c)) + r•c
    rw [map_smul,show (Signed.reflect a).motion (ride a (x i-c))=x i-c from riding a _,smul_sub,sub_add_cancel]
  · intro j
    change Fin.append (fun l : Fin n=>r•x l) (fun l : Fin m=>τ•y l) (Fin.natAdd n j)=_
    rw [Fin.append_right,Points.across_coord,leave]
    change τ•y j=τ•(y j-(r/τ)•c)+r•c
    rw [smul_sub,smul_smul,show τ*(r/τ)=r by field_simp,sub_add_cancel]

/-- The plane lies at physical distance O(r) from the incoming cloud.  The far cloud can be
anywhere in its indicated compact cone at any larger relative date allowed by its clearance. -/
theorem original (F:Spec.Final C f S)(J:ℝ→tower S)(H:Leading F J){n m:ℕ}(a:Axis)(c:E4)(η:ℝ)
    (K:Set (Points n))(L:Set (Points m))(hK:IsCompact K)(hL:IsCompact L)(xSafe:K⊆conf n)(ySafe:L⊆conf m)
    (near:∀x∈K,∀i,x i a<c a)(far:∀y∈L,∀s∈Icc 0 η,∀j,(s•c) a<y j a)
    (v:Fin n→(Bel C.book).Tag)(w:Fin m→(Bel C.book).Tag):
    ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,r/τ≤η → ∀x∈K,∀y∈L,
      ‖S.useAt S (placed r τ x y) (Fin.append (fun i=>physical J r (v i)) (fun j=>physical J τ (w j)))‖≤B:=by
  let A:=inner a c '' K
  let D:=outer c '' ((Icc 0 η) ×ˢ L)
  have hc:IsCompact A:=hK.image (nears a c)
  have hd:IsCompact D:=(isCompact_Icc.prod hL).image (fars c)
  have first:∀z∈A,single z a:=by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨fun i j eq=>xSafe hx (sub_left_inj.mp ((Signed.reflect a).motion.injective eq)),fun i=>?_⟩
    change 0<(ride a (x i-c)) a
    simpa [ride] using near x hx i
  have second:∀z∈D,single z a:=by
    rintro _ ⟨⟨s,y⟩,hy,rfl⟩
    refine ⟨fun i j eq=>ySafe hy.2 (sub_left_inj.mp eq),fun j=>?_⟩
    exact sub_pos.mpr (far y hy.2 s hy.1 j)
  obtain ⟨B,hB,U,hU,bill⟩:=WilsonMacroscopicRichSeparateScales.original F J H a v w A D hc hd first second
  refine ⟨B,hB,U∩Ioi 0,inter_mem hU self_mem_nhdsWithin,?_⟩
  intro r hr τ hτ gap x hx y hy
  let z:=inner a c x;let z':=outer c (r/τ,y)
  have hz:z∈A:=mem_image_of_mem _ hx
  have hz':z'∈D:=mem_image_of_mem _ ⟨⟨(div_pos hr.2 hτ.2).le,gap⟩,hy⟩
  have dilation {l:ℕ}(u:Points l)(hu:single u a)(t:ℝ)(ht:0<t):single (t•u) a:=
    ⟨fun _ _ eq=>hu.1 ((smul_right_injective _ ht.ne') eq),fun i=>mul_pos ht (hu.2 i)⟩
  have law:=F.room.kernel.translations _ _ (spans (dilation z (first z hz) r hr.2) (dilation z' (second z' hz') τ hτ.2)) (r•c)
  rw [location a c r τ hτ.2 x y]
  let l:=Fin.append (fun i=>physical J r (v i)) (fun j=>physical J τ (w j))
  have same:S.useAt S (Points.across (r•c) (closedUp a (r•z) (τ•z'))) l=S.useAt S (closedUp a (r•z) (τ•z')) l:=
    law (fun i=>⟨(l i).1,S.representative _ (l i).2⟩)
  exact (congrArg norm same).le.trans (bill r hr.1 τ hτ.1 z hz z' hz')

end YM.Integration.WilsonMacroscopicRichMovingPlane
