import YM.Integration.WilsonOlderFreshSoftFigureOptics

/-! Absolute zero-moment income of the actual fixed-child planted word, at all ranks including zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftFigureSize
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


open WilsonCoeffUV.Shard

def ink (P:Era G ℝ)(q r:ℕ):ℝ:=∑'z,‖P.2 q r z‖

def gross (g:ℝ)(x:∀i,(F i).Coeff)(P:(∀i,(F i).Index)→Era G ℝ)(q r:ℕ):ℝ:=
  ∑b,‖WilsonOriginalPublicTrialFigure.weight R d g x b‖*ink (P b) q r

theorem original (simple:G.Simple)(e:ℕ)(T:Finset ι)(hh:T.Nonempty)(A τ:ℝ)(a0:0≤A)(τ0:0<τ):
    let L:=R.family.path.levels
    ∀ᶠv:ℕ in atTop,∀(S:Realm G (e+1) Credit.leanC),S.anchor≤v → S.draws=L → S.y=zz L →
      Dormitory S (mass d T) 0 Credit.leanC →
      ∀(N K c:ℕ),v≤c → c≤K → K≤N → ∀β:ℝ,L.clock.hatBeta (v+1)/2≤β →
      L.S.scale K-L.S.scale v≤A*(1+Real.log (L.clock.hatBeta (v+1))) →
      ∀(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(cells:Digits S.draws ι)
        (y:ι → Cover)(f:Pen D T→L[ℝ] ℝ),‖f‖≤1 →
      let P:=fun b=>upper R D d κ pt b S.draws S.paid N cells c K y T f
      ∀q≤e,∀r:ℕ,(∀b,SumBudget (fun z=>‖(P b).2 q r z‖) ((Real.sqrt β)^τ)) ∧
        ∀(g:ℝ)(x:∀i,(F i).Coeff),gross R d g x P q r≤
          (∑b,‖WilsonOriginalPublicTrialFigure.weight R d g x b‖)*(Real.sqrt β)^τ:=by
  intro L
  obtain ⟨B,b1,orders⟩:=WilsonOlderFreshSoftFigureReading.original R D d e
  obtain ⟨U,V,receipt⟩:=orders T hh
  let purchase:=WilsonIndependentCollarOrdinaryWeak.price G (mass d T) e
  let fee:Credit:=⟨0,max 1 (B^T.card),le_max_left ..⟩
  filter_upwards [WilsonIndependentCollarOpticalSpan.original R simple (purchase.prodC fee) A a0 τ τ0] with v paid
  intro S first draw ys dorm N K c vc cK KN β thermal span κ pt cells y f fn P q qe r
  have vK:=vc.trans cK
  have date:v+(K-v)=K:=Nat.add_sub_of_le vK
  obtain ⟨Z,room,small⟩:=paid e S first draw ys (K-v) β thermal (date.symm ▸ span)
  rw [date] at room
  have cc:=receipt S dorm N K c c v first vc le_rfl cK KN Z Z (room.zone vc le_rfl)
    (room.zone le_rfl cK) κ pt cells y f fn
  have Z1:1≤Z:=(S.depth v first).trans (room.year v le_rfl vK)
  have income:purchase.buy Z*B^T.card≤(Real.sqrt β)^τ:=by
    apply le_trans _ small
    rw [Credit.products]
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (Credit.purchase _ Z1))
    change _≤(max 1 (B^T.card))*Z^0
    rw [pow_zero,mul_one]
    exact le_max_right ..
  have stock (b:∀i,(F i).Index):SumBudget (fun z=>‖(P b).2 q r z‖) ((Real.sqrt β)^τ):=by
    have body:Fruit 0 1 0 ((P b).2 q r) (purchase.buy Z*B^T.card):=
      (cc.1 b).2.1 q qe r (Nat.zero_le _)
    have un:=show SumBudget (fun z=>‖(P b).2 q r z‖) (purchase.buy Z*B^T.card) from by
      simpa only [Fruit,Award,hedge,autumn,pow_zero,one_mul] using body
    exact ⟨un.1,un.2.1,un.2.2.trans income⟩
  refine ⟨stock,?_⟩
  intro g x
  rw [gross,Finset.sum_mul]
  exact sum_le_sum fun b _=>mul_le_mul_of_nonneg_left (stock b).2.2 (norm_nonneg _)

end YM.Integration.WilsonOlderFreshSoftFigureSize
end
