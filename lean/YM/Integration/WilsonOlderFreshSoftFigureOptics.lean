import YM.Integration.WilsonOlderFreshSoftFigureReading
import YM.Integration.WilsonIndependentCollarOpticalSpan

/-! The measured colour income, all later scalar feeds and the independent optical tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftFigureOptics
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos PhysicalNext.Repeat.Legato OriginalMarkedSourceComet
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[Fintype ι][LinearOrder ι]
variable (R:Run G)(D d:ι→ℕ)
local notation "F" i:max=>R.family.labels.level (d i)

private def roll (P V U:Credit)(M:ℝ):Credit:=
  ((P.prodC V).prodC U).prodC ⟨0,max 1 M,le_max_left ..⟩

private theorem fare (P V U:Credit)(e q:ℕ)(qE:q≤e)(Z y B t r:ℝ)
    (one:1≤y)(yZ:y≤Z)(B0:0≤B)(pos:0≤r)(small:|t|≤1):
    (∑j∈range (q+1),|t|^j)*(V.buy Z*(U.buy y*r*(P.buy Z*B)))≤
      (roll P V U ((e+1:ℕ)*B)).buy Z*r:=by
  have hZ:=one.trans yZ
  have fees:0≤P.buy Z:=zero_le_one.trans (Credit.purchase _ hZ)
  have uv:0≤U.buy Z:=zero_le_one.trans (Credit.purchase _ hZ)
  have vv:0≤V.buy Z:=zero_le_one.trans (Credit.purchase _ hZ)
  have hsum:(∑j∈range (q+1),|t|^j)≤((e+1:ℕ):ℝ):=calc
    _ ≤ ∑j∈range (q+1),(1:ℝ):=sum_le_sum fun j _=>pow_le_one₀ (abs_nonneg _) small
    _ = ((q+1:ℕ):ℝ):=by simp
    _ ≤ _:=by exact_mod_cast Nat.succ_le_succ qE
  have hU:=Credit.elder U one yZ
  change _ ≤ (((P.prodC V).prodC U).prodC ⟨0,max 1 (((e+1:ℕ):ℝ)*B),le_max_left ..⟩).buy Z*r
  rw [Credit.products,Credit.products,Credit.products]
  simp only [Credit.buy,pow_zero,mul_one]
  change _≤P.buy Z*V.buy Z*U.buy Z*max 1 (((e+1:ℕ):ℝ)*B)*r
  have left:0≤U.buy y:=zero_le_one.trans (Credit.purchase _ one)
  calc
    _ ≤ ((e+1:ℕ):ℝ)*(V.buy Z*(U.buy y*r*(P.buy Z*B))):=mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = P.buy Z*V.buy Z*U.buy y*(((e+1:ℕ):ℝ)*B)*r:=by ring
    _ ≤ P.buy Z*V.buy Z*U.buy Z*max 1 (((e+1:ℕ):ℝ)*B)*r:=by gcongr;exact le_max_right ..

theorem original (simple:G.Simple)(e:ℕ)(T:Finset ι)(hs:T.Nonempty)(A η:ℝ)(a0:0≤A)(η0:0<η):
    let L:=R.family.path.levels
    ∀ᶠ v:ℕ in atTop,∀(S:Realm G (e+1) Credit.leanC),S.anchor≤v →
      S.draws=L → S.y=zz L → Dormitory S (mass d T) 0 Credit.leanC →
      ∀(N K c w:ℕ),v≤w → w≤c → c≤K → K≤N →
      ∀β:ℝ,L.clock.hatBeta (v+1)/2≤β →
      L.S.scale K-L.S.scale v≤A*(1+Real.log (L.clock.hatBeta (v+1))) →
      ∀(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(cells:Digits S.draws ι)
        (y:ι → Cover)(f:Pen D T→L[ℝ] ℝ),‖f‖≤1 →
      let P:=fun b=>upper R D d κ pt b S.draws S.paid N cells c K y T f
      let h:=mass d T
      let H:=fun b=>cruises S.draws S.paid N h c w (P b)
      let full:=fun b=>cruises S.draws S.paid N h c v (P b)
      let retained:=fun b=>cruises S.draws S.paid N h w v (scalarOnly (H b))
      ∀q≤e,∀(t g:ℝ),|t|≤1 → ∀(x:∀i,(F i).Coeff),
        ‖reading R d g x full q t-reading R d g x retained q t‖≤
          (∑b,‖WilsonOriginalPublicTrialFigure.weight R d g x b‖)*
            ((Real.sqrt β)^η*(L.S.a c/L.S.a w)^((4:ℝ)⁻¹)):=by
  intro L
  obtain ⟨B,b1,orders⟩:=WilsonOlderFreshSoftFigureReading.original R D d e
  obtain ⟨U,V,test⟩:=orders T hs
  let P₀:=WilsonIndependentCollarOrdinaryWeak.price G (mass d T) e
  let W:=roll P₀ V U (((e+1:ℕ):ℝ)*B^T.card)
  filter_upwards [WilsonIndependentCollarOpticalSpan.original R simple W A a0 η η0] with v tariff
  intro S first draw ys dorm N K c w vw wc cK KN β thermal span κ pt cells y f fn P h H full retained q qe t g small x
  have vK:=vw.trans (wc.trans cK)
  have date:v+(K-v)=K:=Nat.add_sub_of_le vK
  obtain ⟨Z,room,low⟩:=tariff e S first draw ys (K-v) β thermal (date.symm ▸ span)
  rw [date] at room
  have cc:=test S dorm N K c w v first vw wc cK KN Z Z (room.zone (vw.trans wc) le_rfl)
    (room.zone le_rfl (wc.trans cK)) κ pt cells y f fn
  have live:=S.depth w (first.trans vw)
  have charged:=fare P₀ V U e q qe Z (S.y w) (B^T.card) t (S.tempC w c) live
    (room.year w vw (wc.trans cK)) (pow_nonneg (zero_le_one.trans b1) _) (Real.exp_pos _).le small
  refine (cc.2 q qe t g x).trans (mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun _ _=>norm_nonneg _))
  apply charged.trans
  have hr:S.tempC w c=(L.S.a c/L.S.a w)^((4:ℝ)⁻¹):=by
    change trailC S.draws.S w c=_
    rw [draw,trail_ratio]
  rw [←hr]
  exact mul_le_mul_of_nonneg_right low (Real.exp_pos _).le

end YM.Integration.WilsonOlderFreshSoftFigureOptics
end
