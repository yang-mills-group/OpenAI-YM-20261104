import YM.Integration.WilsonPointChildWidthEntrance
import YM.Integration.WilsonPointChildWidthMinimum

/-! The rooted, positive-width theorem on the actual normalized fixed-child field.
    The two zero-width invoices refer to that same dated program and transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildWidthHistory
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonNeutralPointCourse WilsonPointChildFiledPress WilsonPointChildNormalizedWidth WilsonPointChildWidthPortfolio
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

private theorem powered {x y v:ℝ}{j k:ℕ}(hx:0≤x)(xy:x≤y)(cap:j≤k)(hv:1≤v):
    x*v^j≤y*v^k:=mul_le_mul xy (pow_le_pow_right₀ hv cap)
      (pow_nonneg (zero_le_one.trans hv) _) (hx.trans xy)

private theorem gross {u w:ℕ}{day l M c I A B θ:ℝ}(day1:1≤day)(dl:day≤l)(M1:1≤M)
    (cn:0≤c)(paid:I≤M*l^u)(_ip:0≤I)(an:0≤A)(bn:1≤B)(θn:0≤θ):
    1+max 1 (I*(c*day^w)*((1+A)*B^θ)) ≤
      (2*max 1 c*M*l^(u+w))*(1+A)*B^θ:=by
  have one:1≤l:=day1.trans dl
  let C:=max 1 c*M*l^(u+w)
  let S:=(1+A)*B^θ
  have S1:1≤S:=one_le_mul_of_one_le_of_one_le (by linarith) (Real.one_le_rpow bn θn)
  have C1:1≤C:=one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left ..) M1) (one_le_pow₀ one)
  have cpos:0≤ max 1 c:=zero_le_one.trans (le_max_left ..)
  have grossed:I*(c*day^w)≤C:=calc
    _≤M*l^u*(max 1 c*l^w):=mul_le_mul paid
      (mul_le_mul (le_max_right ..) (pow_le_pow_left₀ (zero_le_one.trans day1) dl _) (by positivity) cpos)
      (by positivity) (mul_nonneg (zero_le_one.trans M1) (pow_nonneg (zero_le_one.trans one) _))
    _=C:=by dsimp [C];rw [pow_add];ring
  have unit:1≤C*S:=one_le_mul_of_one_le_of_one_le C1 S1
  have cap:=max_le unit (mul_le_mul_of_nonneg_right grossed (zero_le_one.trans S1))
  calc
    _≤2*(C*S):=by change 1+max 1 (I*(c*day^w)*S)≤_;linarith only [unit,cap]
    _=_:=by dsimp [C,S];ring

private theorem terminal {day l c:ℝ}(v:ℕ)(cn:0≤c)(day1:1≤day)(dl:day≤l):
    1+max 1 (c*day^v)≤(2+c)*l^v:=by
  have pow1:1≤l^v:=one_le_pow₀ (day1.trans dl)
  have fee:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans day1) dl v) cn
  have bound:max 1 (c*day^v)≤(1+c)*l^v:=max_le
    (one_le_mul_of_one_le_of_one_le (by linarith) pow1)
    (fee.trans (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans pow1)))
  linarith only [pow1,bound]

variable {G:Gauge}{d D:ℕ}
variable (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)(o:Loc G 1)
local notation "A" => R.family.path.levels
local notation "Λ" => RG16.Lambda A
local notation "F" => R.family.labels.level d

def Income (E:ℕ):Prop:=∃M:ℝ,∃v:ℕ,1≤M ∧ ∀ᶠj:ℕ in atTop,
  (∀N,j≤N→∀digit:∀i,Site (R.family.S.block i),Wallet o F (filed R wood a depth digit N j) 0 E (M*(Λ j)^v)) ∧
  (∀N,j<N→∀digit:∀i,Site (R.family.S.block i),invoice F (transfer R wood a depth digit N j)⁻¹ E ≤ M*(Λ j)^v)

theorem original (simple:G.Simple){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (Λ j))
    (E:ℕ)(old:Income R wood a depth o E){η:ℝ}(accuracy:0<η):
    ∀ᶠj:ℕ in atTop,∀N,j≤N→∀digit:∀i,Site (R.family.S.block i),
      Wallet o F (filed R wood a depth digit N j) (width R j) E (((A).clock.hatBeta j)^η):=by
  obtain ⟨M,u,M1,dated⟩:=old
  obtain ⟨k₀,dates⟩:=eventually_atTop.mp dated
  obtain ⟨g,h,gn,bare⟩:=WilsonPointChildTerminalWidth.original R wood a depth o simple granted E
  obtain ⟨k₁,born⟩:=eventually_atTop.mp bare
  obtain ⟨k,kl,kt,entry,fees⟩:=((eventually_ge_atTop k₀).and ((eventually_ge_atTop k₁).and
    ((WilsonPointChildWidthEntrance.original R wood a depth o simple granted E).and
      (WilsonPointChildWidthPortfolio.original R wood a depth o simple granted E)))).exists
  let X:=Tour R k
  let B (z:X)(j:ℕ):=WilsonPointChildWidthMinimum.price o F (filed R wood a depth z.digit z.cutoff j) (width R j) E
  let L (_:X)(j:ℕ):=M*(Λ j)^u
  have resource (j:ℕ):=WilsonPointChildWidthPurchase.prices R granted j
  have day1 (j:ℕ):1≤ max 1 (ageZ ((A).clock.hatBeta j)):=le_max_left ..
  have clock1 (j:ℕ):1≤Λ j:=(day1 j).trans (resource j).2.2.2
  have signed (z:X)(j:ℕ)(kj:k≤j)(live:j≤z.cutoff):=WilsonPointChildWidthMinimum.paid o F
    (filed R wood a depth z.digit z.cutoff j) (width R j) E (entry z j kj live)
  have low (z:X)(j:ℕ):0≤L z j:=mul_nonneg (zero_le_one.trans M1) (pow_nonneg (zero_le_one.trans (clock1 j)) u)
  obtain ⟨c,v,cn,pay⟩:=fees L B (fun z j _ _=>low z j) (fun z j kj live=>(signed z j kj live).1)
    (fun z j kj live=>(dates _ (by omega)).1 _ live z.digit)
    (fun z j kj live=>(signed z _ (by omega) live).2.1)
  let T:=2*max 1 c*M
  have tn:0≤T:=mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left ..))) (zero_le_one.trans M1)
  let cap:=1+(1+M)+T+(2+g)
  have c1:1≤cap:=by dsimp [cap];linarith only [M1,tn,gn]
  let J:=u+v+h
  have Tcap:T≤cap:=by dsimp [cap];linarith only [M1,gn]
  have Acap:1+M≤cap:=by dsimp [cap];linarith only [tn,gn]
  have gcap:2+g≤cap:=by dsimp [cap];linarith only [M1,tn]
  filter_upwards [eventually_ge_atTop k,WilsonPinnedWidthCalendar.original R simple slow J c1 accuracy]
    with i ik close
  intro N live digit
  let z:X:=⟨N,ik.trans live,digit⟩
  let n:=N-i
  have endAt:i+n=N:=by dsimp [n];omega
  let grossFee (j:ℕ):=T*(Λ j)^(u+v)
  have D1 (j:ℕ):0<grossFee j:=mul_pos (by dsimp [T];positivity) (pow_pos (zero_lt_one.trans_le (clock1 j)) _)
  have funded:=close n (width R) (B z) (fun j=>1+L z j) grossFee (resource i).2.1
    (fun j ij jn=>by
      have endj:j≤z.cutoff:=by change j≤N;omega
      have p:=resource j
      have bp:1≤B z j:=(signed z j (ik.trans ij) endj).1
      refine ⟨p.1,p.2.2.1,zero_lt_one.trans_le bp,by linarith only [low z j],?_⟩
      have pow1:1≤(Λ j)^u:=one_le_pow₀ (clock1 j)
      calc
        1+L z j≤(1+M)*(Λ j)^u:=by dsimp [L];linarith only [pow1]
        _≤_:=powered (by linarith only [M1]) Acap (by dsimp [J];omega) (clock1 j))
    (fun j ij jn=>by
      have jl:j<N:=by omega
      have endj:j<z.cutoff:=jl
      let θ:=WilsonPinnedWidthTransport.fraction R.family.S (width R) j
      have θn:0≤θ:=by
        dsimp [θ,WilsonPinnedWidthTransport.fraction]
        exact div_nonneg (resource j).1.le (mul_nonneg (Nat.cast_nonneg _) (resource (j+1)).1.le)
      have inv:invoice F (transfer R wood a depth z.digit z.cutoff j)⁻¹ E ≤ M*(Λ j)^u:=
        (dates j (kl.trans (ik.trans ij))).2 _ jl _
      refine ⟨D1 j,powered tn Tcap (by dsimp [J];omega) (clock1 j),?_⟩
      exact ((signed z j (ik.trans ij) endj.le).2.2 _ (pay z j (ik.trans ij) endj)).trans
        (gross (day1 j) (resource j).2.2.2 M1 cn inv (zero_le_one.trans (invoice_pos ..))
          (low z (j+1)) (signed z _ (by omega) endj).1 θn))
    (by
      rw [endAt]
      have birth:=(signed z N (ik.trans live) le_rfl).2.2 _ (born N (kt.trans (ik.trans live)) digit)
      exact birth.trans ((terminal h gn (day1 N) (resource N).2.2.2).trans
        (powered (by linarith only [gn]) gcap (by dsimp [J];omega) (clock1 N))))
  exact mono (signed z i ik live).2.1 funded

end YM.Integration.WilsonPointChildWidthHistory
