import YM.SignedWilsonExpansion.Contrast
namespace YM.SignedWilsonExpansion.AxialBill
/-! # Independent order-two pure difference prior to smearing
    Log scale positive orientation length exponent.
    Uses on theory of the *same measured detector convention* via `PhaseTilt`.
    Vacuum products imply insensitivity to lower-rank components tested. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token
open WickFace PhaseTilt Contrast
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {O:Booked (Press.portDeck G)}(M:MS_Data G O)(Y:Initialize G){V:Normalize.Store G}(K: Rose.Pick V)
variable (S:Land.Prescription (Press.portDeck G))(h:G.Simple)(hs:TaylorOKF M (Press.wickInput Y) S)(hr:Favors.Horder S)(hu: Ace.UnitP S)
variable (x:Stage 3) (t:ℝ)
local notation "π" => Extent.token
local notation "θ" => Fin 3
local notation "Ξ" => PowerSeries.coeff
local notation "Φ" => Manifest.response
local notation "X" => Xi G
local notation "E" => WickFace.lens G
local notation "U0" => testE G 3
local notation "Ψ" => Facets.posing
local notation "Ω" => leaf G 4
local notation "B" => Sec G 4
-- cancels Fourier weight and accounts for directions
include S M h hs
lemma cancel (p:B) : π t 12 * X (Ψ t x) p=X x p:= by
   refine WickFace.at_low (V:=ℂ) h ( π t 12 • X (Ψ t x) ) (X x) ?_ ?_ p
   · rw [LinearMap.smul_apply, Contrast.bell_unit,Contrast.bell_unit, smul_zero ]
   intro i j; let v:= glow G i j; change π t 12 * X ( Ψ t x ) v=X x v
   have he(x:Stage 3): X x v=∑ a:Fin 3,iris x (update U0 a v):= by
       unfold Xi; rw [ LinearMap.sum_apply ]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [ LinearMap.sub_apply,LinearMap.smul_apply, iris3 ]; rw [ show coin x a v=0 from WickFace.single_off (G:=G) x a .. ]; rw [smul_zero,sub_zero]
   rw [he,he, Finset.mul_sum ]; refine Finset.sum_congr rfl fun a _=>?_ ; let v0:= update U0 a v; have ht:= iris_s (O:=O) M Y S h hs x v0 t
   rw [show Level.Dial 4 t ∘ v0=(fun i=> π t 4 • v0 i) from ?_, MultilinearMap.map_smul_univ ] at ht; swap;
   · funext b; by_cases H:b=a; · simp only [v0,comp_apply,H,update_self]; exact WickFace.money t i j
     simp only [v0, comp_apply,update_of_ne H]; exact WickFace.money t 3 3
   change π t 12 * iris (Ψ t x) v0=_; rw [ show π t 12=∏ i:Fin 3,π t 4 from (by rw [Fin.prod_univ_three]; unfold Extent.token; ring) ]; exact ht
local notation "ξ" => Measure.start Y K 4
local notation "η" => Measure.outlook Y K 4
variable (ν:ℝ)
local notation "u" => Equator.wave ν M 4
local notation "P" => GroupS.gaugeM Y K M ν
local notation "θ₀" => (Ξ 2 ( P (-1) 4) )
include hr hu ν
lemma snapshot (x:Stage 3):
     StarGround ξ ∧ StarGround η ∧ ξ 3 x 1=0 ∧ η 3 x 1=0:= by
    obtain hF:= PhaseTilt.order_first h M ν Y K S hs hr hu x; exact ⟨ Measure.dawn Y K ν M S h hs hr hu, Measure.scaled_sigma Y K ν M S h hs hr hu, hF.2 ⟩
local notation "Θ" => (Ξ 2)
def contrast (F:Way G 4)(s:ℝ)(x:Stage 3)(i:ℕ):ℂ:= (PowerSeries.coeff i) (track F x)-Extent.token (-s) 12*Ξ i (track F (posing (-s) x)) -- ambiguity
lemma seats (x:Stage 3):
     Θ ( track ξ x )-Θ ( track u x)=Xi G x (( Ξ 2 ( Measure.liftT K ν M 4 ) ) E) ∧
     Θ ( track η x )-Θ ( track u x)=Xi G x (( Ξ 2 ( Measure.Z Y K ν M 4 ) ) E):= by
    obtain hF:= PhaseTilt.order_first h M ν Y K S hs hr hu x
    obtain hp:= snapshot M Y K S h hs hr hu ν x; have hS:= Equator.before ν M (d:=4)
    exact ⟨ Contrast.second_gap hp.1 hS hF.2.1 hF.1 ( Measure.charges Y K ν M S h hs hr hu ) ( fun _=> PhaseTilt.settle h M ν Y K S hs hr hu .. ),
            Contrast.second_gap hp.2.1 hS hF.2.2 hF.1 ( Measure.litZ Y K ν M S h hs hr hu ) ( fun _=> PhaseTilt.settled' h M ν Y K S hs hr hu .. ) ⟩
lemma clocked : contrast u t x 2=t • Xi G x (θ₀ E):= by
    have he(y:Stage 3) := (PhaseTilt.order_first h M ν Y K S hs hr hu y).1; rw [ contrast, ← Contrast.scales_opp ];
    have hp:= Equator.before ν M (d:=4); rw [ Contrast.second_gap hp (Manifest.fuel u M Y S h hs hp (-t)) (he x) (?_ : scaling (-t) u 3 x 1=0) ((Scale.Precise.mainM ν Y K M S h hs hr hu).paid (-t) 4 ) ( fun p=> PhaseTilt.tilt_two h M ν Y K S hs hr hu (-t) x p ), PhaseTilt.portwise h M ν Y K S hs hr hu ]; -- fix hp
    · -- scaling1
      unfold Facets.scaling; rw [he]; rfl
-- because params unreferenced need include ν for clock not needed? seats uses ν

lemma agree : contrast ξ t x 2=t • X x (θ₀ E) ∧ contrast η t x 2=t • X x (θ₀ E):= by
    obtain he:= seats M Y K S h hs hr hu ν x; obtain ht:= seats M Y K S h hs hr hu ν (Ψ (-t) x); rw [ ← clocked M Y K S h hs hr hu x t ν ]; unfold contrast; have hp (F:Way G 4)(p:B)(a:Θ ( track F x )-Θ ( track u x )=X x p)(b:Θ ( track F ( Ψ (-t) x) )-Θ ( track u ( Ψ (-t) x))=X (Ψ (-t) x) p): Θ (track F x)- π (-t) 12 * Θ ( track F ( Ψ (-t) x))=Θ (track u x)-π (-t) 12 * Θ (track u (Ψ (-t) x)):= by rw [ sub_eq_iff_eq_add.mp a, sub_eq_iff_eq_add.mp b,mul_add,cancel M Y S h hs x ]; abel
    exact ⟨ hp ξ _ he.1 ht.1,hp η _ he.2 ht.2 ⟩
lemma free (F:Way G 4)(hf:StarGround F): contrast F t x 0=0:= by unfold contrast; rw [ ← Contrast.scales_opp,fee0 hf,fee0 ( Manifest.fuel F M Y S h hs hf (-t) ),sub_self ]
lemma freeze : contrast ξ t x 0=0 ∧ contrast η t x 0=0 ∧ contrast ξ t x 1=0 ∧ contrast η t x 1=0:= by
    obtain ⟨hf,hg, he,hE⟩:= snapshot M Y K S h hs hr hu ν x; obtain ⟨_,_,hv,hV⟩:=snapshot M Y K S h hs hr hu ν (Ψ (-t) x); refine ⟨ free M Y S h hs hr hu _ _ ν ξ hf, free M Y S h hs hr hu _ _ ν η hg,?_ ⟩ ; unfold contrast; rw [ fee1 he, fee1 hE,fee1 hv,fee1 hV ]; simp
omit M h Y S hs hr hu ν
abbrev κ2 (p:Stage 2)(i j:Fin 2) : B→ₗ[ℂ]ℂ:= dyad p i j (lens G).val ∘ₗ coeS 4
abbrev pairField (p:Stage 2) : B→ₗ[ℂ]ℂ:= κ2 p 0 1+ κ2 p 1 0
local notation "f" => PairWave.dd G
local notation "N" => Fintype.card G.ColorIndex
variable (p:Stage 2)
private lemma ready (i:Fin 2)(v:B): iris p ( update f i v ) = κ2 p i (i+1) v:= by apply congr_arg (moment G p.val); funext k; fin_cases i <;> fin_cases k <;> rfl
lemma Epair (H: WickFace.Holds p) : iris p ( PairWave.dd G )= (( (N*2*pay p 0 1^2:ℝ) ):ℂ ):= by
    rw [← show update f 0 E=f from update_eq_self .., ready ]; change dyad p 0 1 (E).val (E).val=_; rw [dy_bill p 0 1 (by decide) H]; simp only [ bitT, ↓reduceIte,one_mul ]
lemma tempo_pair (A:FieldEnd G 4): Φ p f A=pairField p (A E):= by unfold Manifest.response; simp only [LinearMap.coe_mk,AddHom.coe_mk, Fin.sum_univ_two,ready ]; rfl
include h
lemma ep_pos (H: WickFace.Holds p): 0 < ( iris p ( PairWave.dd G ) ).re:= by rw [ Epair p H, Complex.ofReal_re ]; have hx:= positive p 0 1 (by decide); have hv:0<N:= Fintype.card_pos_iff.mpr ( Landau.Detect.color_ne h ); positivity
lemma assertPair (H: Holds p) (hu0:Holds x) (m:B): X x m* (2*iris p f) =3*iris x U0 * pairField p m:= by
    rw [ mul_comm ( X x m ) ]; refine WickFace.at_low h ( ((2:ℂ)*iris p f) • (Xi G x) ) ((3*iris x U0) • pairField p) ?_ ?_ m -- commutes
    · rw [ LinearMap.smul_apply, LinearMap.smul_apply, Contrast.bell_unit x ]; unfold pairField; rw [LinearMap.add_apply];
      have hx(i j:Fin 2)(h:i≠j): κ2 p i j Ω=0:= (dropI p (E).val i j h).trans (single_off (G:=G) p j 3 3);
      rw [hx 0 1 (by decide),hx 1 0 (by decide) ]; simp
    · intro i j; rw [LinearMap.smul_apply,LinearMap.smul_apply, Xi, LinearMap.sum_apply,iris_lens x hu0,Epair p H]; unfold pairField; rw [LinearMap.add_apply];
      have hp(a b:Fin 2)(ha:a≠b): κ2 p a b (glow G i j)= (( ( bitT i * bitT j )*(N*2*pay p a b^2):ℝ ):ℂ):= dy_bill p a b ha H ..
      have hh(a:Fin 3): triple x a (glow G i j)=(↑((bitT i*bitT j)*(N*8*pay x a (a+1)* pay x a (a+2)* pay x (a+1) (a+2)):ℝ):ℂ):= tri_bill x a _ _ ((by decide: ∀ a:Fin 3,a ≠ a+1) a) ((by decide: ∀ a:Fin 3,a+1≠a+2) a) ((by decide: ∀ a:Fin 3,a≠a+2) a) hu0 i j
      simp only [ hp 0 1 ( by decide ), hp 1 0 (by decide), LinearMap.sub_apply, LinearMap.smul_apply, show ∀ a:Fin 3, coin x a ( glow G i j)=0 from fun a=> single_off (G:=G) x a .., smul_zero,sub_zero,hh ]; rw [ Fin.sum_univ_three ]; have h1 : pay x 1 0=pay x 0 1:= pay_m ..
      -- normalize sums
      norm_num only [ Fin.isValue ] -- fin add.Lean simp disch
      simp only [ show (0:Fin 3)+1=1 from rfl,show (1:Fin 3)+1=2 from rfl,show (2:Fin 3)+1=0 from rfl,show (0:Fin 3)+2=2 from rfl,show (1:Fin 3)+2=0 from rfl,show (2:Fin 3)+2=1 from rfl,h1, pay_m x 2 0,pay_m x 2 1,pay_m p 1 0, smul_eq_mul ]; push_cast; ring
-- filmed diagnostic linear relation only, evaluate one such pair on reference, store many if desired.
include M Y S hs hr hu ν
local notation "Z2" => (Ξ 2 ( GroupS.gaugeM Y K M ν (-t) 4))
lemma chargeP (H: WickFace.Holds p) : pairField p (θ₀ E)=(-( (2:ℝ)*(OrderHigh.kinetic G + OrderHigh.locus G))) • iris p f:= by
    obtain ⟨d,he⟩:= WickFace.gap p H 1 0; have hv:d≠0:=fun h=> (sub_ne_zero.mpr ((show Injective p.val.ofLp from p.property).ne ( show (1:Fin 2)≠0 from by decide ))) ( he.trans (h ▸ zero_smul _ _)); rw [ ← tempo_pair _ θ₀, ← PhaseTilt.tilt_two h M ν Y K S hs hr hu (-1), Equator.clocks ν M Y S h hs, show ν- (-1)=ν+1 from (by ring), PairWave.charged M ν p S Y h hs d 1 hv he,Equator.before ]; simp only [one_mul, neg_mul ]
def amplitude (G:Gauge):ℝ:= G.casimir/(16*Real.pi^2)
lemma delta_at (hs1:Holds x): X x (θ₀ E)= amplitude G • iris x U0:= by
    let p: Stage 2:= ⟨ pairPoints (0:E4) (basis 3), pair_ok (Ne.symm (fun h=>?_ )) ⟩; swap; · have ht:=basis_norm (3:Axis); rw [h,norm_zero] at ht; norm_num at ht
    have hp: Holds p:= by intro i; fin_cases i; exacts [ ⟨ (0:ℝ), (zero_smul ℝ _).symm⟩,⟨ (1:ℝ), (one_smul ℝ _).symm⟩ ]
    obtain hc:= chargeP M Y K S h hs hr hu ν p hp; apply mul_right_cancel₀ (show 2*iris p f≠0 from mul_ne_zero (by norm_num) (by intro he; have hp:= ep_pos h p hp; rwa [he, Complex.zero_re, lt_self_iff_false] at hp)); rw [ assertPair h x p hp hs1, hc ]; unfold amplitude OrderHigh.kinetic OrderHigh.locus; rw [ FVA2.Lambda.Gaussian.b0 ]; simp_rw [Complex.real_smul]; push_cast; ring
lemma axial (H:Holds x): contrast ξ t x 2=( ( t*G.casimir/(16*Real.pi^2)):ℝ ) • iris x U0:= by
    rw [ agree M Y K S h hs hr hu x t ν|>.1, delta_at M Y K S h hs hr hu x ν H,smul_smul ]; unfold amplitude; congr 1; ring
end
end YM.SignedWilsonExpansion.AxialBill
