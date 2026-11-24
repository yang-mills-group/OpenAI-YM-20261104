import YM.Pert.Triangle.Identities
import YM.Pert.Parity.Twinning
/-!
Candidate first moment inputs bUU, and sign reversal on their rows even after arbitrary finite square calibration by parity-equivariant tests. A connected response may be made separately by cumulants. No nonvanishing coefficient nor identification of a new coupling inferred from parity alone.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Pert.Triangle
open Lattice Labels Position Function Filter Set Topology Full RawLabels Parity
open scoped Topology Classical ContDiff
variable {G : Gauge} (F : Frames G) {N : Side}
variable (o : Fin 3→Site N)

def triad (j : Fin 3) : Pol G:= if j=0 then bFan G else uMinus G
def sent : Fin 3→Label G 6 := fun j=> if j=0 then oddSlot G else raiseLabel G (by decide) (evenSlot G)
def basic : Fin 3 → E F 6 := enroll F 6 ∘ sent
lemma oddity' : Coat F 6 ∘ basic F = fun i=> if i=0 then -basic F i else basic F i := by
  funext i; by_cases h:i=0
  · subst i; simp only [Function.comp_apply,basic,sent,if_true,Coat_inherit,bFan_sign,map_neg]
  have he : ∀ q : Labels.Label G 4, wash G 6 (raiseLabel G (by decide) q)= raiseLabel G (by decide) (wash G 4 q) := fun _=> rfl
  simp only [Function.comp_apply,basic,sent,h,↓reduceIte,Coat_inherit,he,uMinus_sign]
lemma bare_own (j) : sections 6 F (basic F j)=triad j := by
  have odd := odd_read F (n:=6) le_rfl
  have even := even_read F (n:=6) (by decide : 4≤6)
  by_cases h:j=0 <;> simp only [basic,comp_apply,sent,triad, h,↓reduceIte]
  · exact odd
  exact even
lemma triad_amplitude (L : ℝ) : amplitude (fun _=>6) L Finset.univ o (triad (G:=G)) = row 6 F L o (basic F) := by rw [row_def, show sections 6 F ∘ basic F = _ from funext (bare_own F)]
lemma multilinear_sign {n : ℕ} (Q : Conditions F 6 n) (s : Fin Q.slots) (hp : Q.arity s=3) (b : Ledger Q) (u : (i : Fin (Q.arity s))→E F 6) :
    menu Q b s (fun i=>if i.val=0 then -u i else u i) = -menu Q b s u := by
  let k : Fin (Q.arity s) := ⟨0,hp ▸ (by decide : 0<3)⟩
  let f := menu Q b s
  change f _ = _
  rw [show (fun i:Fin (Q.arity s)=>_)=(fun i=>(if i.val=0 then (-1:ℂ) else (1:ℂ)) • u i) from funext fun i=>by split <;> simp_all, f.map_smul_univ,Finset.prod_eq_single_of_mem k (Finset.mem_univ _)]
  · rw [if_pos (rfl:k.val=0),neg_one_smul]
  intro v _ hv; exact if_neg (fun e=>hv (Fin.ext e))

def catalog (p : Fin 3→E F 6) (f : Points 3→ℂ) : Conditions F 6 1 where
  slots := 1
  arity _ := 3
  columns _ := p
  profiles _ := f
  chisels := LinearMap.id

def candidate (f : Points 3→ℂ) := catalog F (basic F) f
lemma chart_reversal (f : Points 3→ℂ) (v : Ledger (candidate F f)) (b : Buffer F 6) : chart (reverseRows (candidate F f)) (v,b) = -chart (candidate F f) (v,b) := by
  let Q:=candidate F f
  funext i; change Complex.re (decode Q v (i:=i) (fun j=>motor F b (Coat F 6 _))) = -(Complex.re (decode Q v (i:=i) (fun j=> motor F b _)))
  rw [← menu_def, ← menu_def]
  have he (j : Fin (Q.arity i)) : (reverseRows Q).columns i j = (Coat F 6) (basic F j) := rfl
  have hh : (fun j:Fin (Q.arity i)=>(motor F b) ((Coat F 6) (basic F j)))=fun j=> if j.val=0 then -motor F b ((basic F) j) else motor F b ((basic F) j) := funext (fun j=>congrArg _ (congrFun (oddity' F) j) |>.trans (by split_ifs with h h2; rw [map_neg]; exact False.elim (h2 (congrArg Fin.val h)); exact False.elim (h (Fin.ext ‹_›)); rfl)) -- replace
  change Complex.re (menu Q v i (fun j:Fin 3=> (motor F b) ((Coat F 6) (basic F j)))) = _
  erw [hh,multilinear_sign F Q i rfl];rfl
include F
variable {F} {d : ℕ} (Q : Conditions F 6 d) {φ : Ledger Q → Buffer F 6} (f : Points 3→ℂ)
def bareResponse (L : Side) (i p k : ℕ) : ℝ := readJet φ p k (chart (candidate F f)) (finite Q L i) (finite (candidate F f) L i) 0 -- evaluates a `Fin 1` function
lemma reversed_jet (L i p k) : bareResponse Q (φ:=φ) f L i p k = -(readJet φ p k (chart (reverseRows (candidate F f))) (finite Q L i) (finite (reverseRows (candidate F f)) L i) 0) := by
  let X:=candidate F f
  let b t := φ (curve (finite Q L i) p t)
  change _ = -( (iteratedDeriv k (fun t:ℝ=> chart (reverseRows X) (curve (finite (reverseRows X) L i) p t,b t))) 0 0)
  rw [show (fun t=>chart (reverseRows X) (curve (finite (reverseRows X) L i) p t,b t))= (fun t=> -chart X (curve (finite X L i) p t,b t)) from funext (fun t=> chart_reversal F f _ _),iteratedDeriv_fun_neg,Pi.neg_apply,neg_neg];rfl
include Q
lemma vanishes {J} (h : Fair Q J) (hc : Reports (chart Q) (white Q) 0 φ) (L) (hL : Tendsto (fun i=>finite Q L i 0) atTop (𝓝 (white Q))) (p k : ℕ) (hk : Even k) : ∀ᶠ i : ℕ in atTop, bareResponse Q (φ:=φ) f L i p k=0 := by
  filter_upwards [position_sign h hc L hL (candidate F f) p k] with n hn
  rw [hk.neg_one_pow, one_smul] at hn
  have hw := reversed_jet Q (φ:=φ) f L n p k
  rw [hn,←bareResponse] at hw; linarith
end YM.Pert.Triangle
