import YM.FVA2.Scale.Functions
import YM.PhysMS.Frame.Measured
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size
import YM.Integration.WilsonPositiveMSOnePoint

/-! Each genuine independently registered bare one-point wave is invariant
under signed rotations, at every perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileOnePointWave
open Function Filter Set Finset Table Spec Pert Climb Lattice Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open MS.Dial MS.Rake MS.Book.Convolve MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom
open XSpace XSpace.Normalize FVA2 FVA2.Scale FVA2.Position FVA2.Position.Axes
open private prefix_one empty_head from YM.Integration.WilsonRichFirstConnectedMoments
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) {O : Booked (Press.portDeck G)} (M : MS_Data G O)

def line {A : Type*} [AddCommGroup A] [Module ℂ A] (L : MultilinearMap ℂ (fun _ : Fin 1=>A) ℂ) : A →ₗ[ℂ] ℂ :=
  L.toLinearMap (fun _=>0) 0

theorem read {A : Type*} [AddCommGroup A] [Module ℂ A] (L : MultilinearMap ℂ (fun _ : Fin 1=>A) ℂ) (a : A) :
    line L a=L (fun _=>a) := by
  apply congrArg L
  funext i
  have hi : i=0:=Subsingleton.elim _ _
  subst i
  exact Function.update_self ..

theorem free (d : ℕ) (s : Signed) (v : (Bel C.book).Field d) :
    (Maxwell.Free.fields C.labels d) ((Bel C.book).mirror (spin_free C.labels) d s v)=
      ori s.ortho d ((Maxwell.Free.fields C.labels d) v) :=
  Subtype.ext (address_motion C.labels s v)

include C in
private theorem first (simple : G.Simple) (s : Signed) (v : Sec G 0) : ori s.ortho 0 v=v := by
  let y:=(Maxwell.Free.fields C.labels 0).symm v
  have hy : (Maxwell.Free.fields C.labels 0) y=v := LinearEquiv.apply_symm_apply .. 
  obtain ⟨c,hc⟩:=UVNext.FreeStress.below C.labels simple (by decide : 0<4) y
  have cancel : (Bel C.book).mirror (spin_free C.labels) 0 s y=y := by rw [hc,map_smul,Table.mirror_unit]
  rw [←hy,←free C 0 s y,cancel]

theorem positive (ν : ℝ) (d : ℕ) (x : Scale.Stage 1) (i : Dframe.Toon G d) (hi : 0 < Glyph.size i) (k : ℕ) :
    line (Dframe.meteor ν M d x.val k) (Dframe.theory i)=0 := by
  rw [read]
  let f : Fin 1→Dframe.Toon G d:=fun _=>i
  change Dframe.meteor ν M d x.val k (Dframe.fill f)=0
  rw [Dframe.ribbon]
  let a : Fin 1→MS.Rake.Label (Press.portDeck G):=Dframe.flash ∘ f
  let b:=Arrival.Schedule.plot x.val
  change (Trunk.stack (marked (Fin 1))).cheers (Dial.book M a ν b) ((marked (Fin 1)).grade univ) univ k=0
  have size : (marked (Fin 1)).grade univ=1:=by decide
  rw [size,prefix_one,Pi.add_apply,empty_head _ univ_nonempty,zero_add]
  change Dial.book M a ν b (univ:Finset (Fin 1)) k=0
  rw [show (univ:Finset (Fin 1))={0} by decide]
  exact WilsonPositiveMSOnePoint.connected M a ν (Arrival.Schedule.track x.property) 0 hi k

include C in
theorem wave (simple : G.Simple) (ν : ℝ) (d : ℕ) (s : Signed) (x : Scale.Stage 1) (k : ℕ) (v : Sec G d) :
    Equator.wave ν M d 1 x k (fun _=>ori s.ortho d v)=Equator.wave ν M d 1 x k (fun _=>v) := by
  let B:=Press.portDeck G
  let P:=line (Dframe.meteor ν M d x.val k)
  have main : P.comp (ori s.ortho d)=P := by
    apply (Daylight B d).ext
    intro i
    simp only [LinearMap.comp_apply]
    rw [show (Daylight B d) i=Dframe.theory i from Dframe.theory_sig i]
    by_cases e:i.size=0
    · have fixed (w : Sec G i.size) : ori s.ortho i.size w=w := by
        generalize i.size=t at e w ⊢
        subst t
        exact first C simple s w
      rw [Dframe.include_sig i,Dframe.up_yaw,fixed]
    · have pos : 0 < Glyph.size i:=Nat.pos_of_ne_zero e
      rw [Dframe.yaw,rotateField,map_sum,positive M ν d x i pos k]
      apply Finset.sum_eq_zero
      intro c _
      change (P.restrictScalars ℝ) (_ • Dframe.theory (Axes.take i c))=0
      rw [LinearMap.map_smul]
      change _ • P (Dframe.theory (Axes.take i c))=0
      rw [positive M ν d x (Axes.take i c) pos k,smul_zero]
  have h:=DFunLike.congr_fun main v
  simpa only [Equator.wave,LinearMap.comp_apply,P,read] using h

end YM.Integration.WilsonPositionSeparatedProfileOnePointWave
