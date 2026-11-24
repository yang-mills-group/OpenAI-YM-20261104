import YM.FVAAlt2.First.Signed
import YM.FVAAlt2.Shop.Lobby
/-! Connect individual rank portions to the same normalized expectation.
Lentry and Land-frames normalized via the existing completed tree result.
No Ward/chart shortcut. No ε cut used. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart MS.Native.Draft MS.Menus MS.Local.Physical MS.Landau MS.Landau.Detect MS.Lifting MS.Tone MS.Momentum
open MS.Book MS.Book.Convolve MS.Native.Paint MS.Native.Wilsonian MS.Plane MS.Logarithm MS.Native.Studio
open Pert Pert.Orb SchemeRG11 SchemeRG11.Atoll SchemeRG11.Haze SchemeRG11.Pile SchemeRG11.Sway SchemeRG11.Sway.Lam
open MvPolynomial (X homogeneousComponent)
open PertExtension Precision Ends
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius PowerSeries Classical Matrix
variable {G: Gauge}{d k:ℕ}{L: Frames G}{n:Side}{p q:pLabel G}{B: Deck G} {v:Rake.Label B}
local notation "Φ"=> Dot G Cover
local notation "CZ"=> PowerSeries ℂ
variable (o: Site n)
lemma letterAt (p:pLabel G): moveLetter o (sensorMap 0 p)=sensorMap o p:= by
 funext u; let t:= u ∘ turnAddress o; have he : expandAt 0 t=expandAt o u:=by funext v; simp [expandAt,t,Lattice.affine,turnAddress,add_comm]
 unfold moveLetter; unfold sensorMap; simp only [LinearMap.pi_apply,AlgHom.toLinearMap_apply]; change MvPolynomial.aeval (fun i:Key G=> legAt i 0 t) p=_; simp_rw [← uses_wrap,he] -- simp_rw cycle?
lemma usedHere (p:pLabel G)(hp:p.IsHomogeneous k) (T: Aura (resident p) k) (h:realCast p∈invariantSpace G): AtomCert o (resident p) k (sensorMap o p):= by
 rw [← letterAt]; exact AtomCert.on_aura o (resident p) T _ (sensor_open h 0) ((parallels p).born n).born ((parallels p).born n).home
lemma rent_here (p:pLabel G)(hp:p.IsHomogeneous k) (h:realCast p∈invariantSpace G): AtomCert o (resident p) k (sensorMap o p):= usedHere o p hp (happened hp h) h
abbrev Ctx (j: ℕ)(p:pLabel G): Pol G:= realCast (clip j p)
lemma earns (j:ℕ)(h:realCast p∈invariantSpace G): Ctx j p∈invariantSpace G:= by unfold Ctx clip; rw [LinearMap.comp_apply,← harness, ← utc]; exact SchemeRG11.Sway.homogeneous_inv (SchemeRG11.Sway.dream_inv h _) j
abbrev owes {o:Site n}(u:Rake.Label B)(j:ℕ): Wilson.Config G n→ℝ:= sensorMap o (clip j (price u.item.2))
set_option quotPrecheck false
local notation "A"=> pLabel G
abbrev light (u:Rake.Label B)(j:ℕ):Dot G Cover:= resident (clip j (price u.item.2))
lemma ownsAt(u:Rake.Label B)(j:ℕ): AtomCert o (light u j) j (owes (o:=o) u j):= rent_here _ _ (MvPolynomial.homogeneousComponent_isHomogeneous ..) (earns _ (price_in u.item.2))
open AtomCert
variable {ι κ W:Type} [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (Q₀:Module.Basis ι ℝ (Land G n))(T:Module.Basis κ ℝ (ScalarGhost G n))
include T in
lemma slot_link (p:pLabel G)(hp:p.IsHomogeneous k)(h:AtomCert o (resident p) k (sensorMap o p)) : Ends.ray Q₀ (h.atomSeries Q₀)=Lsup o 1 (realCast p):= by
 let F:=sensorMap o p; let S:=Land G n; let g(t:Land G n):= positiveLinks (g0 G n t); let w: JetArray S:= ray Q₀ (h.atomSeries Q₀); let Y:=PowerSeries.X (R:=ℂ)^k
 have he : ( terrain o 1 (realCast p) ) ∘ g= Complex.ofReal ∘ μy F:= by funext x; exact ( saw_real o p _ ).symm
 have hz(t:S): ChartC (terrain o 1 (realCast p) ∘ g) t = fitR (μy F) t:=he ▸ ( show ChartC (Complex.ofReal ∘ μy F ) t = _ from chart_line (h.stood4.of_le le_top) t ) -- axis parameter
 have hr(t:S): Y*w t=ChartC (terrain o 1 (realCast p) ∘ g) t:= by rw [hz]; rw [mul_comm]; exact Fixed.ray_mark Q₀ T h t
 have ht:=shift_motif (E:=Land G n) (g0 G n) o 1 (p:=realCast p) (hp.map _); rw [show (fun v:S=>terrain o 1 (realCast p) (positiveLinks (g0 G n v)))= terrain o 1 (realCast p) ∘ g from rfl] at ht
 exact funext fun i=> mul_left_cancel₀ (show Y≠0 from pow_ne_zero _ PowerSeries.X_ne_zero) ((hr i).trans (congr_fun ht i))
variable [LinearOrder W][Fintype W] (hn:Admissible n) {D:ChartRatio G}(hD:LocalRatio D)(x:W→Site n)(v:W→Rake.Label B)
abbrev totL (u:Rake.Label B):ℕ:= u.item.1.val
abbrev Ban (u:Rake.Label B):= Fin ( totL u+1 )
abbrev Band (v:W→Rake.Label B):= (i:W)→Ban (v i)
def tile (D:ChartRatio G)(x:W→Site n)(v:W→Rake.Label B)(j:Band v): CZ:= Lobby.ΦbaseT D univ (fun i:W=>( Fin.val (n:=totL (v i)+1) )) (fun i (w:Ban (v i))=> owes (o:=x i) (v i) w.val) j
def enterL (p:Rake.Label B): A:= price p.item.2 -- ℝ-pol
-- beware HP
include T in
lemma clip_link(j:Band v): let h : ∀ i:W,AtomCert (x i) (light (v i) (j i).val) (j i).val ( owes (o:=x i) (v i) (j i).val ):=fun i=>ownsAt (x i) (v i) (j i).val
 Fixed.total Q₀ h univ=∏ i:W,Lsup (x i) 1 (Ctx (j i).val (enterL (v i))):= by
 intro h; funext t; unfold Fixed.total; rw [Finset.prod_apply]; change valS4 Q₀ t _=_; rw [map_prod]; refine Finset.prod_congr rfl fun i _=>?_ ; exact congr_fun ( slot_link (x i) Q₀ T (clip (j i).val (enterL (v i))) (MvPolynomial.homogeneousComponent_isHomogeneous ..) (h i) ) t -- missing include T
include Q₀ T hn hD in
lemma clip_budget(j:Band v): Lentry (∏ i:W,Lsup (x i) 1 (Ctx (j i).val (enterL (v i))))= tile D x v j:= by ext1 k; rw [← clip_link Q₀ T, tile, Lobby.ΦbaseT, PowerSeries.coeff_mk ]; exact Fixed.per hD Q₀ T univ hn _ k
lemma chip_sum(p:pLabel G)(h:p.IsHomogeneous d) : ∑ j:Fin (d+1),Ctx j.val p= dream 1 (realCast p):=by
 simp_rw [Ctx,clip,LinearMap.comp_apply]; rw [utc,← realCast_sum]; apply congrArg realCast
 let P:= (winds G 1).heat p; change ∑ j:Fin _, homogeneousComponent j.val P=P; rw [Fin.sum_univ_eq_sum_range (fun m=> homogeneousComponent m P)];
 apply Eq.trans _ (MvPolynomial.sum_homogeneousComponent P); symm; apply Finset.sum_subset; · exact Finset.range_mono (Nat.succ_le_succ (high_degree _ h))
 intro j _ hj; simp only [mem_range,not_lt] at hj; apply MvPolynomial.homogeneousComponent_eq_zero; have he:P.totalDegree≤d:=high_degree _ h; omega
lemma tabs_sum_map {S:Type*} [Fintype S] (f:S→ Pol G): ∑ i:S,Lsup o 1 (f i)=Lsup o 1 (∑ i:S,f i):=by funext y; unfold Lsup tabs; rw [Finset.sum_apply,map_sum]
lemma summaryL(i:Rake.Label B) :
 ∑ j: Ban i,Lsup o 1 (Ctx j.val (enterL i))=Lsup o 1 (dream 1 (realCast (enterL i))):=by
 rw [tabs_sum_map, show (∑ j:Ban i,Ctx j.val (enterL i))= _ from chip_sum _ (weightR (price_grade i.item.2)) ]
-- Sum integral-entry linear; PS multiply. Sup dosage.Real
lemma entry_sum {S:Type}(A':Finset S)(w:S→ JetArray (Land G n))(hw:∀ s, Pert.Orb.Ready (w s)): Lentry (∑ i∈A',w i)= ∑ i∈A',Lentry (w i):=by
 induction A' using Finset.induction_on with
 | empty=>
    simp only [Finset.sum_empty]
    have he : Pert.Orb.Ready (0:JetArray (Land G n)):=Pert.Orb.Ready.constant _
    have hs:= Lentry_add he he; rw [zero_add] at hs
    exact _root_.add_eq_left.mp hs.symm
 | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi, Lentry_add (hw i) (Pert.Orb.Ready.sum fun j _=> hw j),ih]
include Q₀ T hn hD in
theorem rawTiles : Lentry (∏ i:W,Lsup (x i) 1 (dream 1 (realCast (enterL (v i)))))=∑ j:Band v,tile D x v j:= by
 simp_rw [← summaryL (x _)]; rw [ Fintype.prod_sum, entry_sum ]; exacts [Finset.sum_congr rfl fun j _ => clip_budget Q₀ T hn hD x v j,fun q=> Pert.Orb.Ready.prod (fun i _=> lsup_ready _ _ _) ]
end YM.FVAAlt2.Pairing
