import YM.Integration.WilsonIndependentCollarMovingInk

/-! The literal chronological argument for the selected path census and
its complete log successor, including every previously joined face. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOutputFilm
open Function Finset Lattice Wilson RG Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonReceivedFixedDigitHistory FundedMarkedPathSelection
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} [DecidableEq ι] {D:ι→ℕ} {e:ℕ}

def atChild (V:Realm G (e+1) Credit.leanC)(m:ℕ)(hm:V.anchor ≤ m)(S:Finset ι)(k:ι→ℕ)
    (N d:ℕ)(cell:Digits V.draws ι)(Y:Outerm G D)(well:Wellness k Y)(cut:m+1+d≤N)(A:ℝ)
    (salary:Uniform V (itinerary V.draws V.paid k N cell d (m+1) Y) (m+1) (by omega) A):
    Input V hm S k D A:=
  let H:=itinerary V.draws V.paid k N cell d (m+1) Y
  let ok:Wellness k H:=sound V.draws V.paid k N cell V.hG V.green Y well d (m+1) cut
  {familyAt:=fun y=>H (chartIn (loose V.draws m) y (cell m))
   offsets:=fun _=>cell m
   empty:=fun y=>ok.quiet' (chartIn (loose V.draws m) y (cell m))
   degree:=fun y=>ok.level' (chartIn (loose V.draws m) y (cell m))
   price:=fun y J _ j hj r=>salary (chartIn (loose V.draws m) y (cell m)) J j hj r}

theorem output_atChild (V:Realm G (e+1) Credit.leanC)(m:ℕ)(hm:V.anchor ≤ m)(S:Finset ι)(k:ι→ℕ)
    (N d:ℕ)(cell:Digits V.draws ι)(Y:Outerm G D)(well:Wellness k Y)(cut:m+1+d≤N)(A:ℝ)
    (salary:Uniform V (itinerary V.draws V.paid k N cell d (m+1) Y) (m+1) (by omega) A)(J:Finset ι):
    output (atChild V m hm S k N d cell Y well cut A salary) J N =
      fun y=>itinerary V.draws V.paid k N cell (d+1) m Y y J:=rfl

theorem packets (V:Realm G (e+1) Credit.leanC)(m:ℕ)(hm:V.anchor ≤ m)(S:Finset ι)(k:ι→ℕ)
    (N d:ℕ)(cell:Digits V.draws ι)(Y:Outerm G D)(well:Wellness k Y)(cut:m+1+d≤N)(A:ℝ)
    (salary:Uniform V (itinerary V.draws V.paid k N cell d (m+1) Y) (m+1) (by omega) A)
    (J:Finset ι)(front:ι)(o:Cover):
    packetH J (output (atChild V m hm S k N d cell Y well cut A salary) J N) (mass k J) (e+1) front o =
      packetH J (fun y=>itinerary V.draws V.paid k N cell (d+1) m Y y J) (mass k J) (e+1) front o:=rfl

end YM.Integration.WilsonIndependentCollarOutputFilm
end
