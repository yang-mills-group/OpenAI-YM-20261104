import YM.Frontier6.Multi.Toll.Stamps
import YM.Frontier6.Multi.Bonds.Deep

/-! Delivered birth costs on paths with graded inputs from fixed horizon.
No height or regularity requests tied to the cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Lattice RG Wilson MergeProof Ribbons Canopies Finset Accent Fareway Extra.Histories Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Push Marker Extraction
open scoped Topology BigOperators Classical
variable {I:Type*}{T:Fareway I}{G:Gauge}(C:Family G)(hG:G.Simple)
variable {O:Type}[Fintype O][DecidableEq O] (t:O→ℕ)(d:ℕ) (v:(i:O)→ C.label (t i))(H:Extraction.Order)
variable {a c z ε:ℝ}{j k m:I→ℕ}(hj:Bench C.S T j c)(hm:Bench C.S T m a)(hk:Bench C.S T k z)
variable (x:I→O→ Cover)(hc:C.Makes) (hε:0<ε)(hX:a<1)(hY:1<c)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "Y"=> (fun i: I=> C.S.gridPoint (j i) ∘ x i)

def dept (M:ℕ):= (2*C.S.a M)*(C.path.levels.budget M).B^2

def Aspect (T:Fareway I)(v:I→O→ E4):Prop:= (∀ j:O,T.Costs (fun i=> v i j) (-1))∧ Pairwise (fun j k=> T.Mint (fun i=>‖v i j-v i k‖) (-1))
variable (hr:Realm C)
include hr hc hG hj hm hk hX hY hε
lemma scenery (ht:z<a)(hv:0<z)(h:Aspect T Y) (b:O→ℝ)(root:O)(hh:∀ i,0<b i)(hB:∀ i,(C.labels.level (t i)).coeffSize (v i) ≤ b i) : ∃ Z B:I→ℝ, T.Mint Z (forestPower t a c ε-(d:ℝ)*a) ∧ T.Costs B (-(welcome t d a c z ε)) ∧ (∀ i,0<B i)∧ ∀ᶠ i in T.via, Stamped C (m i) (j i) (k i) t (x i) v H d (Z i) (B i):=by
    obtain ⟨W,r,D,hR,hcol,⟨hV,hP⟩,hI⟩:=hr.launches; obtain ⟨χ,hχ⟩:=hP.mother
    let p i:= Stock.Tabs.chosen A 1 hr.stops (k i); have hp:= chosen C hr.stops hk; let e (i):= Real.exp (T.scale i*(-ε)); let bx i:= Real.exp (T.scale i*(welcome t d a c z ε)); let F i:= charge C t b (j i) (m i) (e i); let z' i:= needQuota C d (m i) (F i); let B i:= 2*(stakes C (k i) (p i) / bx i)
    have hs :T.Mint (fun i=> dept C (j i)) (-c):= (((T.minted_c _ two_pos).mul hj.spacing).mul ((hj.notes (briar C hG hV)).power 2)).eq (by ring)
    have hd : ∀ᶠ i in T.via, Pairwise (fun k l=> dept C (j i) ≤ ‖Y i k-Y i l‖):=by
       have hb : ∀ k l, ∀ᶠ i in T.via, k≠l→ dept C (j i) ≤ ‖Y i k-Y i l‖:= by
          intro k l; rcases eq_or_ne k l with rfl|hf; simp
          exact (hs.cheaper (h.2 hf) (by linarith)).mono fun i hi h=> hi.le
       filter_upwards [eventually_all.mpr (fun k=>eventually_all.mpr (hb k))] with i hi j k h -- pairwise binder implicit ?
       exact hi j k h
    have hβ i:0< B i:=mul_pos two_pos (div_pos (Real.exp_pos _) (Real.exp_pos _))
    have hz':T.Mint z' _:= budget_est C hG t d b hh hj (ε:=ε) hm; have h0:= T.minted (welcome t d a c z ε)
    refine ⟨fun i=>2*z' i,B, (T.minted_c _ two_pos|>.mul hz').eq (zero_add _),?_,hβ,?_⟩
    · have hs:= Fareway.Costs.mul (R:=ℝ) (T.minted_c _ two_pos).pay ((tickets C hr.stops hk hv hG).mul h0.inv.pay)
      simpa only [zero_add,B,bx,div_eq_mul_inv] using hs
    have heB:= toll_paid C hG t d b hh hj hm hε ht hp hR
    have hx:= hm.succ C.path.levels.fits.mesh; have hA:0<c:=zero_lt_one.trans hY
    let J(i):= C.path.levels.budget (m i+1); have heC : T.Mint (fun i=>(C.S.a (m i+1))*((J i).B^2+1:ℕ)) (-a):=by
       push_cast; exact (hx.spacing.mul (((hx.notes (briar C hG hV)).power 2|>.eq (by ring)).common (T.minted_c _ one_pos))).eq (add_zero _)
    have hu:= hx.spacing.div (T.minted_c 8 (by norm_num))
    filter_upwards [ hp.infinite.eventually_ge_atTop (C.ref d), (hI.comp hm.infinite).eventually_ge_atTop (Fintype.card O), heB, eventually_all.mpr (fun i:O=> hj.infinite.eventually_ge_atTop (C.ref (t i))), travelers C hG hV hm hε hA hj, roomed C hm ht hk (lensScope C d), T.ahead, hx.later hj (lt_trans hX hY), hp.later hm ht,heC.cheaper hk.spacing (by linarith),hd,eventually_all.mpr (fun i:O=> (h.1 i).from_allowance hu (by linarith))] with i hi hz h0 he' hp' hy hw hx hT hA' hd hs'
    apply stamper C (m i) (j i) (p i) (k i) d t (x i) v root H hR χ (hχ _) hr.frame hr.stops hc hx (Stock.Tabs.opened _ _ _ _).1 hT.le (Stock.Tabs.opened _ _ _ _) hi he' hz hA'.le hd _ hy (Real.exp_pos _) _ (fun j h=>hp' _ h.le) b hh hB h0.1 rfl (Real.exp_pos _) rfl h0.2.1 h0.2.2
    · intro l; exact le_trans (le_of_eq (mul_comm ..)) ((le_div_iff₀ (by norm_num : (0:ℝ)<8)).1 (hs' l)) -- weird
    exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hw.le (neg_nonpos.mpr hε.le))) -- check
end YM.Frontier6.Road
