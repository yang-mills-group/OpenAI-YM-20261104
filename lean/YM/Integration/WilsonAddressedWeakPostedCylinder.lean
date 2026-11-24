import YM.Integration.WilsonAddressedWeakTerminalPrice
import YM.Next.RANK.Memorandum

/-! The exact resolved original source goes through the compensated physical examiner at the middle mesh. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedWeakPostedCylinder
open Lattice Wilson RG MeasureTheory Marker Cells Next.Rank Next.Rank.Glyph Next.Rank.Exponential
open Next.Rank.Station Next.Rank.Value Next.Rank.Camp Next.Rank.Dock Next.Rank.Read Next.Rank.Peak
open Finset Filter
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {k N p m v:ℕ} {b:ℝ}
variable {D:Rep G (C.side (middle C.path.levels b k) p)} (J:Change D.p m)

def middlePost {x : Points v} (Q : ℕ) (Y : Course C N p k) (hN : k ≤ N) (raw : Config G (C.side N p) → veil (Fin v))
    (B : Fin v → (standard C).Tag) (hx : Fit C.path.levels b k x) : Prop :=
    let T := Ship.yard C b hN p
    let A := C.path.levels
    let P := route A b k p Q D.p.B
    let F := Ship.targets C B hx
    let HI : middle A b k ≤ N := (before A b k).trans hN
    let u := readers (C:=C) (b:=b) (p:=p) x hN HI
    ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ), ∃ (H : ι → SourceAt G u)
      (K : κ → Lifted G u D.p.threshold) (W : T.Cell × flame (Fin v) → SourceAt G u),
      Wells J W (view T F) P ∧ Reception J H K ∧ Background D K ∧
        Y.flow (Array.stamp T (C.beta N p) raw) _ HI = dust D (Sum.elim H W) K

theorem posted {x : Points v} (Q : ℕ) (Y : Course C N p k) (hN : k ≤ N) (raw : Config G (C.side N p) → veil (Fin v))
    (continuous : ∀ i : modes (Fin v), Continuous fun U=>(raw U).part i)
    (B : Fin v → (standard C).Tag) (hx : Fit C.path.levels b k x) (ha : Allowed C.path.levels b k)
    (hm : v ≤ m) (hu : middlePost J Q Y hN raw B hx)
    (hb : 8≤D.p.B) (hh : D.p.B^2+2*(Q*D.p.B)≤(C.path.levels.clock.coverSize k)^10) :
    let A := C.path.levels
    let T := Ship.yard C b hN p
    let l := middle A b k
    let HI : l ≤ N := (before A b k).trans hN
    let X := Array.stamp T (C.beta N p) (fun U=>Poly.pass (-(Ship.targets C B hx))*raw U)
    Notice D (readers (C:=C) (b:=b) (p:=p) x hN HI) (Y.flow X l HI) (fun _ => J.radius) J.e J.output J.hail := by
  intro A T l HI X
  obtain ⟨ι,κ,hι,hκ,H,K,W,hW,h,hB,hD⟩ := hu
  let F := Ship.targets C B hx
  let u := raw
  have hz : F.part (quiet _)=0 := (Read.cumulative C (Station.tested C.path.levels b k x) B _).1
  have hc : ∀ i : modes (Fin v),Continuous fun U => (u U).part i := continuous
  have hv : Y.flow X l HI= fun U => Poly.pass (Array.tilt T F)*dust D (Sum.elim H W) K U := by
    change Y.flow (Array.stamp T (C.beta N p) (fun z => Poly.pass (-F)*u z)) l HI=_
    rw [Array.flow_corr _ _ T hc F hz]; exact funext fun U => congr_arg (Poly.pass _ * ·) (congr_fun hD U)
  rw [hv,catches T F hz]; have hy (i : T.Cell × flame (Fin v)) : sectionAt i = (W i).fires := (hW.lit i).symm
  simp_rw [hy]; exact Dock.grant J (by simpa only [Fintype.card_fin] using hm) (alignment Y hN ha hx hb hh) hW h hB

end YM.Integration.WilsonAddressedWeakPostedCylinder
