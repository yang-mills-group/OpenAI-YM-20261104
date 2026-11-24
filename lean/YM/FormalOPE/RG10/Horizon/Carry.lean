import YM.FormalOPE.RG10.Horizon.Panel
import YM.FormalOPE.RG10.Horizon.Solo

/-!
# Perturbative continuum response sheet for a cluster candidate
All measurements billed at $g_X$, each slot with real formal weights interpreted there except where
a projection sub explicitly acts on $g_X$. Pair time signs included via `swing` before using
these operations; for an exterior normalized to $T=\exp(t)$ its own g_T input weights are shifted
with warp first. This accounts for higher-order designated costs and θ-free data. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Panel
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{R:Rails F} {P:Plan F}{Y:Drivers}{Z:Patience P Y}
  {m n d e k r : ℕ}
local notation "ρ" t=> R.drive t
local notation "W" => R.flow.warp
variable (U: Seats F d) (v : Fin n→ Seats F e) (A : Rear n)
  (s:ℝ)

-- conversion from a shifted-coordinate origin (s taking position order with ratio exp(s))
def trail (R:Rails F) (s:ℝ) (v: Seats F d): Seats F d := (R.flow.warp s ∘ v) ᵥ* (R.drive s d)
def far := trail R (-s) U
lemma unfold_trail : trail R s (trail R (-s) U)= U:=by
 unfold trail
 have he (v:Seats F d)(M:Matrix (Deck F d) (Deck F d) fps): W s ∘ (v ᵥ* M) = (W s ∘ v) ᵥ* M.map (W s) := funext (fun i=>RingHom.map_vecMul ..) 
 rw [he,Matrix.vecMul_vecMul, show ((R.drive (-s) d).map (W s)) * R.drive s d = 1 from Apertures.Halo.extern_inv R d s]; simp_rw [Matrix.vecMul_one,Function.comp_def,R.ok.neutral]


lemma through_trail (h:d ≤ k): trail R s (promote h U) = promote h (trail R s U):= by
 have hp : W s ∘ promote h U = promote h (W s ∘ U):= by
    apply unique ?_ (proceeds ..); constructor;
    · intro i; exact congr_arg (W s) ((proceeds ..).1 i)
    intro i hi; simp only [Function.comp_apply, (proceeds h U).2 _ hi,map_zero]
 unfold trail; rw [hp,stationed]
variable (R Z)

def see (t:Test (m+n)) (x : Fin m→Seats F d) :=
 detect R Z t (Fin.append (promote (le_max_left d e) ∘ x) (promote (le_max_right d e) ∘ v))
lemma extension (t:Test (m+n)) (x : Fin m→Seats F d) (h:d ≤ k) (h':e ≤ k) : see R Z v t x = detect R Z t (Fin.append (promote h ∘ x) (promote h' ∘ v)):= by
 unfold see; rw [← across _ _ _ (max_le h h')]
 congr 1; ext1 i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [composed]

variable {R Z}
lemma moved (hs:Street Z R) (t: Test (m+n))(x:Fin m→Seats F d) :
   R.flow.warp s (see R Z v t x)=see R Z (trail R s ∘ v) (Next.UVStress.dilate (Real.exp_pos (-s)) t) (trail R s ∘ x) := by
 unfold see; rw [warp hs]; apply congr_arg; ext1 i; refine Fin.addCases ?_ ?_ i<;> intro j <;> simp only [Fin.append_left,Function.comp_apply, Fin.append_right]; exacts [through_trail ..,through_trail ..]

-- Linear on the center when being used with a single label. Recombine estimates.
def found (R : Rails F) (Z:Patience P Y) (A: Test (1+n))(v:Fin n→Seats F e)(V:Seats F d) := see R Z v A (fun _:Fin 1=>V)
private lemma edited {X:Type*}(V U:X)(v:Fin n→X): update (Fin.append (fun _:Fin 1=>V) v) (@zeroAt n) U = Fin.append (fun _=>U) v := by
 ext1 i; refine Fin.addCases ?_ ?_ i
 · intro i; fin_cases i; simp [zeroAt]
 intro i; simp [zeroAt, update_of_ne (show Fin.natAdd 1 i ≠ Fin.castAdd n 0 from fun h=>by have hx:= congr_arg Fin.val h; simp at hx)]
variable (R Z) {s A v}
def promoting (hf:d ≤ e) : (Seats F d)→ₗ[fps] Seats F e where
  toFun := promote hf
  map_add' x y:= by unfold promote; simp [Pi.single_add, sum_add_distrib]
  map_smul' c x:= by unfold promote; rw [RingHom.id_apply]; simp only [Finset.smul_sum, Pi.smul_apply,Pi.single_smul] -- inspect

def seen (x: Test (1+n))(v:Fin n→Seats F e): (Seats F d)→ₗ[fps] fps:= by
 let d':= max d e; let u:= promote (le_max_right d e) ∘ v; let a:= fun w=>R.adjust Z d' ⟨⟨_,x⟩,w⟩
 exact ((program a).toLinearMap (Fin.append (fun _:Fin 1=> (0:Seats F d')) u) zeroAt).comp (promoting (le_max_left ..)) -- #check
lemma seen_on (x: Test (1+n))(v:Fin n→Seats F e)(U: Seats F d):seen R Z x v U = found R Z x v U:= by
 unfold seen
 rw [LinearMap.comp_apply]
 simp only [MultilinearMap.toLinearMap_apply,edited]; exact program_eq .. 

namespace Consumer
-- Exterior far-probe data. `horizon` fixed. Input coordinates retaining all slots and geometry.
structure Vantage (F:Frames G) where
  legs : ℕ
  rear : Rear legs
  horizon : ℕ
  fields : Fin legs → Seats F horizon
variable (X: Vantage F)(t:ℝ) (E : Fore m) (x : Fin m→ Seats F d)
local notation "χ" => trail R (-t) ∘ X.fields

def burst := if h:E.budget < Real.exp t * X.rear.gap then see R Z χ (Arrangements.test E X.rear t h) x else 0 -- nondegenerate t enough

def imply (X : Vantage F)(t:ℝ) (d:ℕ) := seen R Z (silver X.rear t) (trail R (-t) ∘ X.fields) (d:=d)

def lean (d:ℕ) := seen R Z (soloTest X.rear) X.fields (d:=d)
lemma same_budget {V:Seats F d} {h:d ≤ k} : imply R Z X t k (promote h V) = imply R Z X t d V:= by
  unfold imply; rw [seen_on,seen_on, found,found];
  erw [extension R Z (k:=max k X.horizon) _ _ _ (le_max_left ..) (le_max_right ..), extension R Z (k:=max k X.horizon) _ _ _ (h.trans (le_max_left ..)) (le_max_right ..)]
  simp_rw [Function.comp_def, composed]
variable {Z R}
lemma shape_cost (h:Street Z R) : W t (imply R Z X t d U)=lean R Z X d (trail R t U) := by
 rw [imply,lean,seen_on,seen_on,found,found, moved (m:=1)];
 simp_rw [silver, Apertures.round _ _,Function.comp_def, unfold_trail];
 exact h
end Consumer
end YM.FormalOPE.RG10.Panel
