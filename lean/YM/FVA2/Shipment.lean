import YM.FVA2.OrbitPlanet
import YM.FVA2.ColumnPrice
import YM.FormalOPE.RG10.Sync.Bills

/-!
# Same source assembly from the open conditional construction (MS-collared and reachable)

Track weight update as a FUNCTION of full coarse field (off all parent trees). `Journey`
uses exactly the RG10 `OpenSlots.Broadcast`. Cohesive: no choice of covariance or
clock at higher horizon invalidates lower powers. Use actual `Fk.read/Stem` as the
top conditional formula with bare top transition. `EqBook` below identifies the
inversion joint coefficient `purchase` on any given history with the same labels using
`Stamp.shafts`. Vary penalty clocks and history if desired; key observable invariance
(Passenger) to all perturbative orders.

At present do not assume comparison of DIFFERENT-regulator seam Fk coefficients,
e.g. Analytics uses full Torus conditionals. These are exact identities among bare
coefficients, support communications at formal level. Unconditioning of the actual
finite normalized series of couplings with quantitative analytic bounds is NOT needed or
requested at this point. Do not use as such.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Shipment
open RayScatter
open Function Filter Topology Metric Finset PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Blocking FormalOPE.RG10.Sync
open Lattice Gauge Precision Fabric Inherit PertExtension PertExtension.Chart GaussianScore RG InversionTop
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {c f n:Side}{G:Gauge}{S:StepData c f}
variable {P:Inside S.ratio}{t:S.Choices}{H:S.patch.Branches S.kernel G}
local notation "μ"=> tangent G (Blocking.Index S P)
open Source
variable (I:Type) {L: Fabric G n}(F:Cloth L)(J:ChartRatio G)(hJ:LocalRatio J)(w:L.Accounts→PowerSeries ℝ)(hp:∀ i,0< Series.Tested.term ( w i ) 0)(h0:w none=1)
section credit
open Router
variable {q a : ℕ}
omit I
variable {E V Rα : Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup V][NormedSpace ℝ V]
lemma boost_X (d:E→ₗ[ℝ] V) (u:Ticket V): boost d (X^q*u) = X^q*(boost d u) := by rw [map_mul,map_pow,boost, map_X]
lemma transferX {R:Type} [CommRing R] [CommRing Rα] (F:R→+Rα) (u:PowerSeries R):
 throughPrice F (X^q*u)= X^q*(throughPrice F u):= by apply PowerSeries.ext; intro i; unfold throughPrice; rw [coeff_X_pow_mul']; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk,coeff_mk,coeff_X_pow_mul']; split; rfl; exact map_zero _
variable {Θ:Unmasked G f}{x:PowerSeries ℝ}{A: Ticket (Flats G f)}
def Alive {P:Inside S.ratio}{t:S.Choices} {Θ:Unmasked G f}{x:PowerSeries ℝ} := ( Quadratic.core (gated P Θ t x)).RespectsPrice

abbrev burn (a:ℕ) (u:Wilson.Observable G n) := MultiGauge.Stack.drop a (imprintRoot u)

lemma dragX (h:( Quadratic.core (gated P Θ t x)).RespectsPrice): Broadcast P t J x Θ h (boost (blankRight P) ( X^q * A)) = X^q * Broadcast P t J x Θ h (boost (blankRight P) A) := by rw [Broadcast,Broadcast,boost_X]; unfold Quadratic.fit; rw [ mul_left_comm _ (X^q), show (gated P Θ t x).uptake μ h ( X^q * _ ) = X^q * _ from transferX _ _, mul_assoc ]; rfl

lemma courseX {n:Side}{L:Fabric G n}(F:Cloth L) (u:Unmasked G n)(x:L.Cost→PowerSeries ℝ) (A:Ticket (Flats G n))(h:Commission J F u x): course F x u J ( X^q * A) h = X^q * course F x u J A h:= by
   cases F with
   | floor=> rw [course,course]; simp_rw [boost_X, enjoy]; rw [ mul_left_comm _ ( X^q ), Stack.taking, mul_assoc ] -- dependent β
   | @inLayer c f S H t hf L P C=> rw [ course,course ]; rw [ dragX J ( P:= P ) ]; exact courseX ..
termination_by structural F
lemma purchaseX (q:ℕ)(A:Ticket (Flats G n)): purchase F w hp hJ (X^q*A)=X^q*purchase F w hp hJ A:= courseX ..
include h0 in
lemma passBurn {u:Wilson.Observable G n}(a: ℕ) (hu:Orb.PreTest u)(h:X^a * burn a u=imprintRoot u): purchase F w hp hJ (burn a u) = MultiGauge.Stack.drop a (PowerSeries.mk (Orb.diag (Orb.restrictedO u))) := by
     rw [ ← diagram F w hp hJ h0 hu, ← h,purchaseX,Stack.drop_mul ]

lemma boost_through (g:E→ₗ[ℝ] V) {A B:Ticket V}(h:Through q A B): Through q (boost g A) (boost g B):= by intro i hi; unfold boost; rw [coeff_map,coeff_map,h i hi]
lemma current_through (h:( Quadratic.core (gated P Θ t x)).RespectsPrice) {A B:Ticket (Flats G f)} (hp:Through q A B):
      Through q (Broadcast P t J x Θ h (boost (blankRight P) A)) ( Broadcast P t J x Θ h (boost (blankRight P) B)) := ( keepsThrough _ (h:=Through.mul (Through.refl (receipt P t J x Θ)) (boost_through (blankRight P) hp)) ).mul (Through.refl _) -- placeholder
lemma consistent {n:Side}{L: Fabric G n}(F: Cloth L) (u:Unmasked G n)(x:L.Cost→PowerSeries ℝ)(h: Commission J F u x){A B:Ticket (Flats G n)}(hp:Through q A B): Through q (course F x u J A h) (course F x u J B h):= by
   cases F with| floor=> rw [course,course]; unfold enjoy; refine Through.mul ?_ (Through.refl _); apply keepsThrough; exact (Through.refl _).mul (boost_through _ hp) | inLayer P C=> rw [ course,course ]; exact consistent C _ _ _ (current_through J _ hp)
termination_by structural F
lemma purchase_consistent {A B:Ticket (Flats G n)} (h:Through q A B): Through q (purchase F w hp hJ A) (purchase F w hp hJ B):= consistent _ _ _ _ _ h
end credit

section scenes
variable {B: MS.Local.Physical.Deck G} (D: NativeDictionary B)
variable {W: Type} [DecidableEq W] (d:W→ℕ) ( y:W→Site n) (A:(i:W)→MS.Menus.Glyph B (d i)) (s:Finset W)
local notation "Sκ"=> Channel.Seals D y d A
local notation "Yκ"=> Stamp.shafts Sκ s
local notation "dκ"=> Stamp.degrees Sκ s
local notation "µκ"=> Stamp.pre_all Sκ s

def Up : Ticket (Flats G n):= ∏ i∈s, burn ((Sκ i).slots) ( Sκ i ).stencil -- slots actual.Cost lower.

lemma set_min {a: Weights G} {M:MS.Native.Dot G Lattice.Cover} {x:Site n}(h:Brand M a) {g:ℕ}(hd:MS.Book.From M.val g)(i:ℕ)(hp:i<g): coeff i (imprintRoot (put a x) ) = 0:= by
    unfold imprintRoot Stack.imbed Stack.rise; apply Subtype.ext; rw [coeff_mk]; funext y; change Series.Radial.jet _ i y= _; let p:=Trans.coverL G n
    have he: (( (put a x) ∘ Orb.liftLinks) ∘ expLinks G (Orb.OEdge n))= (put a x ∘ MS.Native.Chart.nation) ∘ p.toContinuousLinearMap:= funext fun i=> congr_arg _ (Trans.assemble_exp G n i)
    rw [ he, GermLaplace.jet_pull p.toContinuousLinearMap _ ((Source.pos_jet h x).of_le le_top) y, Source.below h x hd i hp ]; rfl

-- inscription only.Wick unaffected
omit [DecidableEq W] in
lemma sealBurn (i:W) : X^( Sκ i ).slots * burn (( Sκ i ).slots) ( Sκ i ).stencil = imprintRoot ( Sκ i ).stencil := by unfold burn; apply MultiGauge.Stack.recover; let a:=A i; exact fun j hj=> set_min (D.stamps a.size a.grade a.2.2) (D.book.levels ..).low j hj
include F
omit [DecidableEq W] in
lemma ignition : X^dκ * Up D d y A s= imprintRoot Yκ:= by unfold Up Stamp.degrees Stamp.shafts; rw [ ← prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, rootOfProduct F s _ (fun i _=> (Sκ i).test) ]; simp_rw [ sealBurn D d y A ]
include h0 hJ
-- pre-log transmission in primitive, same at every horizon.
omit [DecidableEq W] in
theorem manifested : purchase F w hp hJ (Up D d y A s)= Channel.realRead Sκ s := by
    unfold Channel.realRead; rw [ ← diagram F w hp hJ h0 µκ, ← ignition F,purchaseX, Stack.drop_mul ] -- exact capsule
omit h0 hJ

-- direct same object characteristic in Fk.read.Origin ray along V.Month metrics permits.
omit hp w F
variable {L': Fabric G c} (T:Cloth L') (hf:Even f.val) (z:W→Site f)(v:Flats G c)
local notation "Ωκ"=> OrbitPlanet.frame P t v
local notation "ρ"=> Channel.Seals D z d A
variable (P H t)
include H hf T hJ
omit [DecidableEq W] in
theorem first_step : Stack.read v (Broadcast P t J 1 (initialFull G f 1) (OrbitPlanet.billedStep P t H L' T hf) (boost (blankRight P) (Up D d z A s))) = PowerSeries.mk ( RGComparison.Core16.Lumen.Fk.read Ωκ J (OrbitPlanet.tagAll P) (OrbitPlanet.book P (Stamp.shafts ρ s)) (Stamp.degrees ρ s) ):= by
    have h:OrbitPlanet.distinct (Stamp.shafts ρ s):= OrbitPlanet.distinctProduct _ s (fun i _=> OrbitPlanet.distinct_source (x:=z i) (hp:=D.stamps (A i).size (A i).grade (A i).2.2)) -- binder names
    rw [ OrbitPlanet.arrival P t H _ _ hJ _ T hf _ h, ← ignition (F:=Cloth.inLayer (t:=t) (b:=H) (h:=hf) P T) (D:=D) (y:=z), dragX,map_mul,map_pow,show ∀ v:Flats G c,Stack.read v X=X from fun v=> PowerSeries.map_X _, Stack.drop_mul ] -- type
end scenes
end YM.FVA2.Shipment
