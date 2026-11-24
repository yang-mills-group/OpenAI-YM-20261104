import YM.Qlocal.Moonset.Hark
/-!
# The same model curvature expansion through formal coupling re-expression

Operates on the entire vertex kernel. Computing the jets on **global log-link coordinates** of
any supported period; current convergence here is that of `Stanza`, not of the actual field
series. Goal identity with the `LocalFormal` Reset clock (the `Caliber`). This does not assume the
actual coupling obeys this clock. Far/winding comparison at the formal port remains with the
prescribed projection uncertainty (`Prices`). Here exact, before feeding THAT receipt.

`transfer` is explicit forward equality through order `p`. No approximate elimination of terms
with powers higher than p in the formal check. Need identify ages of output `winding` via
`Boreal.prices`; no name change in markers on this calendar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Wilson Lattice RG Gauge Push.AbsoluteSums Finset Marker
open AllOrder AllOrder.Floe AllOrder.Floe.Pace
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern Quipu.Eluder
open Precision Exterior PertExtension.Series
open Incline Bookworm Primitives.TwoWave Primitives.TwoWave.RealSlice AllOrder.Ker
open Comparison.RG02 Comparison.RG02.Assembly
open Comparison.RG02.Adjacent Comparison.RG02.Moving.Path Comparison.RG02.Moving.Shift
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {V:Type} [Fintype V][DecidableEq V] {R:Marker.Census V} {G:Gauge}
variable {g:V→ℕ}{p i k L:ℕ}(Y : Stanza R G g p)
variable {t a C : ℝ} (s:Senses R) {n: Side} (o:V → Site n) (N:ℕ)
set_option quotPrecheck false
local notation "C'" => Lagger.dues g s.val
local notation "T" => Stanza.son Y N
local notation "K" => p+C'+1
local notation "X" => fieldDir G n 1
local notation "Π" => rule (Coarse G) n
local notation "I" => ports G n
local notation "φ" => art Y s o (fun _=>True) N
variable (t : ℂ) (hp:(Stanza.son Y N).Allows a C)(ha:0<a)
/-- Grasp at mark coordinates unchanged; the leading normalization of `grasp0` extracts the
 prefactored jet with its marker power shift (the supplied ordinary coupling units). -/
noncomputable def data : Display (rule (Coarse G) n):=fun i x=> t*Complex.ofReal (Anthem.grasp0 (Stanza.son Y N) o s i x)
noncomputable abbrev tag(term i k:ℕ)(x:rule (Coarse G) n):ℂ:= t*Complex.ofReal (Assembly.jet (art Y s o (fun _=>True) N i k) term (ports G n x))
-- explicitly ages of a rank contribution
include hp ha
local notation "B!"=> data Y s o N t
local notation "F'"=> tag Y s o N t
variable (q : Coin) (q₀ : q 0=0) (r:ℕ) (hr:p ≤ r) (i:ℕ)(x:rule (Coarse G) n)
local notation "D" => (calibration q).direct r
lemma situate (i:ℕ)(hi:i ≤ p) : data Y s o N t i x=∑ e∈range (i+1),∑ k∈range (p+C'+1), tag Y s o N t (i-e+k) e k x := by
 unfold data; rw [book_identity Y s o N hp ha x i hi]; simp_rw [Complex.ofReal_sum,Finset.mul_sum]; rfl
omit hp ha in
lemma posting (e i k:ℕ) (δ u:ℝ) : (↑(δ*(D).rating u):ℂ)^i * F' (i-e+k) e k (((D).rating u)⁻¹ • x) = ((↑δ:ℂ)^i * ↑(tags 0 i (i-e+k) ((D).rating u)))* F' (i-e+k) e k x:= by
 unfold tags tag; rw [map_smul, Clipper.weight]
 push_cast
 simp_rw [zpow_zero,one_mul,smul_eq_mul,Complex.ofReal_mul]; push_cast; ring
lemma turned (u:ℝ): ages (B!) 0 p u ((D).rating u) x=∑ i∈range (p+1),∑ e∈range (i+1),∑ k∈range (p+C'+1), Adjacent.money D 0 i (i-e+k) u * F' (i-e+k) e k x:= by
 unfold ages cover; rw [zpow_zero,Complex.ofReal_one,one_mul]; refine Finset.sum_congr rfl (fun i hi=>?_); rw [situate Y s o N t hp ha (((D).rating u)⁻¹ • x) i (Nat.le_of_lt_succ (mem_range.mp hi))]; simp_rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _=> Finset.sum_congr rfl fun k _=> posting Y s o N t q r x e i k u u
-- summing the triangular slot set on renormalization orders
omit hp ha in
private lemma convolution {E:Type*}[AddCommMonoid E] (d:ℕ) (f g:ℕ→ℕ→E) (h:∀ i ≤ d, ∀ e ≤ i, f i e=g (e+d-i) e):
  (∑ i∈range (d+1), ∑ e∈range (i+1), f i e) = ∑ i∈range (d+1), ∑ e∈range (i+1), g i e:= by
  let h' (f:ℕ→ℕ→E):=(∑ i∈range (d+1), ∑ e∈range (i+1), f i e)
  have he (f:ℕ→ℕ→E):h' f=∑ e∈range (d+1),∑ i∈Icc e d, f i e:=by
     let a:=range (d+1); apply Eq.trans (b:=∑ i∈a,∑ e∈a, if e ≤ i then f i e else 0) (Finset.sum_congr rfl fun i hi=>?_)
     · rw [Finset.sum_comm]; unfold a; refine Finset.sum_congr rfl fun e he=>?_ ; rw [← Finset.sum_filter, show ((range (d+1)).filter fun i=>e ≤ i)=Icc e d from (by ext; simp only [mem_filter,mem_range, Finset.mem_Icc]; omega)]
     unfold a at *; rw [← Finset.sum_filter, show ((range (d+1)).filter fun e=>e ≤ i)=range (i+1) from (by ext; simp only [mem_filter,mem_range]; have := mem_range.mp hi; omega)]
  rw [show (∑ i∈range (d+1),_)=h' f from rfl,show (∑ i∈range (d+1),∑ e∈range (i+1), g i e)=h' g from rfl, he f,he g]
  refine Finset.sum_congr rfl (fun e he=>Finset.sum_bij (fun i _=> e+d-i) ?_ ?_ ?_ ?_)
  all_goals simp only [Finset.mem_Icc] at *
  · intro i hi; omega
  · intro i a j b; omega
  · intro i hi; exact ⟨e+d-i, by omega, by omega⟩
  intro i hi; exact h i hi.2 e hi.1
local notation "ρ"=>Moonset.forward q
lemma transmitted (d e j:ℕ) (he:e ≤ p) : tag (toChild q Y) s o N t d e j x= ∑ i∈range (e+1), (ρ i j (e-i):ℂ) * tag Y s o N t d i j x := by
 change t*Complex.ofReal (Radial.jet (art (stencil (ρ) Y) s o (fun _=>True) N e j) d ((I) x))= _
 rw [jet_retains Y s o _ N hp ha ((I) x) _ e d j he,Complex.ofReal_sum,mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Complex.ofReal_mul,mul_left_comm]; rfl
include q₀ hr
local notation "h₀"=> Pace.Coin
lemma lower_display (hi:i ≤ p) : born (data Y s o N t) D 0 p i x= data (toChild q Y) s o N t i x:= by
  let K':= K; let F:=F'; let W(j e k:ℕ)(u:ℝ):= Adjacent.money D 0 j (j-e+k) u*F (j-e+k) e k x
  have hn (j e k:ℕ): ContDiffAt ℝ ω (W j e k) 0:= (monetized ..).mul contDiffAt_const
  let f j e:= ∑ k∈range K',motion (W j e k) i
  have hW j e k : motion (W j e k) i=(motion (Adjacent.money D 0 j (j-e+k)) i)*F (j-e+k) e k x:= by
    rw [show W j e k=(fun u=> F (j-e+k) e k x * Adjacent.money D 0 j (j-e+k) u) from funext fun i=> mul_comm .., mscale _ (monetized ..),mul_comm]
  let yc:=toChild q Y; let M:= ∑ v:Senses R,Lagger.dues g v.val
  have hE (v:Senses R): Lagger.dues g v.val ≤ M:= Finset.single_le_sum (f:=fun v:Senses R=> Lagger.dues g v.val) (fun i _=> Nat.zero_le _) (mem_univ v)
  have hp':= retain_price Y (Moonset.forward q) M C hE hp
  let f' j k e:= (ρ e k (j-e):ℂ)*F (i-j+k) e k x
  let g' j e:=∑ k∈range K',f' j k e
  calc
    _= ∑ j∈range (p+1),∑ e∈range (j+1),f j e:= by
      unfold born; simp_rw [turned Y s o N t hp ha q r x]
      let H j e u:=∑ k∈range K',W j e k u; have hK j e : ContDiffAt ℝ ω (H j e) 0:= ContDiffAt.sum fun k _=>hn j e k
      change motion (fun u=>∑ j∈range (p+1),∑ e∈range (j+1),H j e u) i=_; rw [msum _ (fun j u=>∑ e∈range (j+1),H j e u) fun j _ => ContDiffAt.sum fun e _=> hK j e]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [msum _ _ (fun e _=> hK j e)]; exact Finset.sum_congr rfl fun e _=> msum _ _ fun k _=> hn j e k
    _= ∑ j∈range (i+1),∑ e∈range (j+1),f j e:= Eq.symm (Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hj'=> by unfold f; have h0: ¬ j ≤ i:= mt (Finset.mem_range.mpr ∘ Nat.lt_succ_of_le) hj'; simp_rw [hW, Adjacent.triangular,if_neg h0,zero_mul,Finset.sum_const_zero]))
    _= ∑ j∈range (i+1),∑ e∈range (j+1),g' j e:= by
      apply convolution; intro j hj e he; apply Finset.sum_congr rfl; intro k hk; unfold f'; erw [hW j e k, motion_paid q q₀ r e k i j _ hj ((Nat.sub_le i _).trans (hi.trans hr)) (by omega)]; simp_rw [show e+i-j-e=i-j by omega,show i-(e+i-j)+k=j-e+k by omega]
    _= _ := by
      rw [situate yc s o N t hp' ha x i hi]
      exact Finset.sum_congr rfl (fun j hj=> (Finset.sum_comm (f:=fun e k=> f' j k e)).trans (Finset.sum_congr rfl (fun k hk=> Eq.symm (transmitted Y s o N t hp ha q x (i-j+k) j k ((Nat.le_of_lt_succ (mem_range.mp hj)).trans hi)))))
lemma transfer (hi:i ≤ p) : born (data (toParent q Y) s o N t) D 0 p i x=data Y s o N t i x:= by
  let y:=toParent q Y; let M:= ∑ v:Senses R,Lagger.dues g v.val
  have hE (v:Senses R): Lagger.dues g v.val ≤ M:= Finset.single_le_sum (f:=fun v:Senses R=> Lagger.dues g v.val) (fun i _=>Nat.zero_le _) (mem_univ v)
  have hp':= retain_price Y (raise q) M C hE hp; have H:= retain_price y (ρ) M _ hE hp'
  rw [lower_display y s o N t hp' ha q q₀ r hr i x hi,situate (toChild q y) s o N t H ha x i hi,situate Y s o N t hp ha x i hi]; refine Finset.sum_congr rfl (fun j hj=> Finset.sum_congr rfl (fun k hk=>?_)); let Z:ℕ→Prop:=fun _=> True; unfold tag; rw [show art (toChild q y) s o Z N j k =art Y s o Z N j k from ?_]; exact funext fun u=> recovers Y s o _ (represent u) N q q₀ j k ((Nat.le_of_lt_succ (mem_range.mp hj)).trans hi) hp ha
end YM.Qlocal.Moonset
