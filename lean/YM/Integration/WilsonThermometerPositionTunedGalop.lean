import YM.Integration.WilsonThermometerPositionTunedPublicCharge

/-! The genuine seven original finite graded position words on Galop's own
lower-corrected fields and coupling reannouncements. The difference still
contains the actual normalized original group response at each fired basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionTunedGalop
open Finset XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Photo
open XSpace.Tornado XSpace.AxesTangent XSpace.Retirement WilsonMaxwellThermometerInteracting
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (W:Initialize G) {V:Normalize.Store G}
variable (x:Sample 3) (p:Tags G 6 3) (e:ℕ) (S:Finset (Fin 3))
def filed (read:Tags G 6 3 → Finset (Fin 3) → PowerSeries ℂ) : ℂ :=
  ∑ f∈tally e 3, if ∀i:Fin 3,i∉S→f (some i)=0 then
    PowerSeries.coeff (f none) (read (pulseU f (deck (V.layout W (grab x) 6)) p) S)
  else 0

def originalRead : ℂ := filed W (V:=V) x p e S
  (WilsonThermometerPositionTunedPublicCharge.submitted R W 6 x)
def loss : ℂ := filed W (V:=V) x p e S
  (WilsonThermometerPositionTunedPublicCharge.signed R W 6 x)

theorem face : originalRead R W (V:=V) x p e S -
    WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p e S = loss R W (V:=V) x p e S := by
  unfold originalRead loss filed WilsonMaxwellThermometerPublicGalop.quotient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs
  · rw [← map_sub,WilsonThermometerPositionTunedPublicCharge.ordinary]
  · rw [sub_zero]

/-- One scalar on the complete signed three-input reading. The numerical model
repeats the same corrected mesh submission on every proper face. -/
theorem first_order :
    let X:=originalRead R W (V:=V) x p
    let Q:=WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p
    let J:=loss R W (V:=V) x p
    first (X 0) (X 1) - WilsonMaxwellThermometerPublicGalop.node W (V:=V) x p =
      first (X 0) (J 1) + (first (X 0) (Q 1) - first (Q 0) (Q 1)) := by
  intro X Q J
  have h (s:Finset (Fin 3)) : X 1 s=Q 1 s+J 1 s := by
    have eq:=face R W (V:=V) x p 1 s
    change X 1 s - Q 1 s=J 1 s at eq
    linear_combination eq
  change first (X 0) (X 1)-first (Q 0) (Q 1)=_
  simp only [first,h]
  ring

end YM.Integration.WilsonThermometerPositionTunedGalop
end
