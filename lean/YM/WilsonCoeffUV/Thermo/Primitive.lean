import YM.WilsonCoeffUV.Thermo.LimitSlots
/-!
# Canonical thermodynamic recursion

Assume actual common flat step hypotheses separate. Does not yet select kinetic
read or perform output/reset. Also export operator as a function of independent
matrix mean, flat next, contour. Allows fixed-order charge limits later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Next.Free Tree PowerSeries AnalyticNext.QuarticMatch.Sheets
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{L n f:Side} {α β V ι : Type*}{k r l j:ℕ}

def plaster (G:Gauge)(R:FaceRow):= coloration G (α':=Hooks G) (β':=Hooks G) id id (hBlock R)
def plain (G:Gauge)(R:FaceRow):= shuttleM (plaster G R)
lemma plaster_fee {K:FaceRow}{s A : ℝ}(h:K.strip s A)(he:0≤s)(ha:0≤A): (plaster G K).strip s (kinPrice s A):= coloration_paid id id _ (kinPrice_nn _ _ ha) (hBlock_width he h)
lemma plain_fold (G:Gauge){K:FaceRow}{s A:ℝ}(h:K.strip s A)(he:0<s)(ha:0≤A): Pilots (fun n=> precisionC G n K) (plain G K):=by
  have he n: (plaster G K).acts n=precisionC G n K:= by ext i j; rw [plaster,coloration_act,hBlock_periods he.le h]; rfl
  simp_rw [←he]; exact matrix_visit (plaster_fee h ‹0<s›.le ha) ‹0<s› (kinPrice_nn _ _ ha)
lemma plain_cost (G:Gauge){K:FaceRow}{s A:ℝ}(h:K.strip s A)(he:0≤s)(ha:0≤A): dragCup terrain s (kinPrice s A) (plain G K):= matrix_width (plaster_fee h he ha) (kinPrice_nn _ _ ha)
lemma flatY {K:(n:Side)→ ropes (Site n) α α} {U:ropes Cover α α}(h:Pilots K U)(k r): Yields (fun n=> flatPal (K n) k r) (flatPal U k r):= by
  by_cases he:k=0 <;> simp only [flatPal, he, ↓reduceIte]; swap; · exact Yields.zero
  by_cases hz: 2=r
  · subst r; simp_rw [shine_lit]; exact h.orb
  simp_rw [shine_dark (k:=2) hz]; exact Yields.zero
lemma costY (U:PowerSeries ℝ)(i r): Yields (fun n:Side=>uband (U:=Co n α) (Fintype.card (Site n) • U) i r) (uband (U:=Cloth α) U i r):=by
  cases r with
  | zero=>
    have he n v: dilute (fun n:Side=>uband (U:=Co n α) (Fintype.card (Site n) • U) i 0) n v=coeff i U:= by
      simp only [dilute,↓reduceIte, uband,Pi.smul_apply,shine_lit]; rw [map_nsmul,nsmul_eq_mul,smul_eq_mul,inv_mul_cancel_left₀ (show (Fintype.card (Site n):ℝ)≠0 by positivity)]
    refine ⟨fun x=>?_, Eventually.of_forall fun _ _ _=> congr_arg _ (Subsingleton.elim ..),1,‖coeff i U‖,one_pos,Eventually.of_forall fun n=> ⟨norm_nonneg _,fun x=>?_⟩⟩
    · simp_rw [he,uband,shine_lit]; exact tendsto_const_nhds
    rw [he]; simp [soar,league]
  | succ r=> simp_rw [uband,shine_dark (show 0≠r+1 by omega)]; exact Yields.zero

section
variable {P:Patch}{C:KernelChoices}
local notation "Ñα"=> Hooks G
local notation "Ñβ"=> Co P.L (Hooks G)
local notation "Ñγ"=> Hinge G P.L

abbrev Canvas (G:Gauge):= Pal ℝ (YForest G)
abbrev Crude (G:Gauge):= (n:Side)→ PChart G n
abbrev Scroll (G:Gauge)(P:Patch):= Pal ℝ (Cloth (Hinge G P.L))

variable (P) (C) (Ñ:ChartRatio G)

def stellar (M:ropes Cover Ñβ Ñα)(W:Canvas G): Scroll G P:=
    (fun i=>prism (upper 1 M) (plants P.L (bearingJ Ñ i))) -
    (fun i=>prism (stair (upper 1 M) ladder) (scrub (warren P C G) i))-
    fun i=>prism (upper 1 M) (plants P.L (scrub W i))

def spurs (Γ:ropes Cover Ñβ Ñβ)(M:ropes Cover Ñβ Ñα)(W:Canvas G): Layers ℝ (Cloth Ñγ):= tide (stair (upper Γ 0) 0) (stellar P C Ñ M W)

def snow (Γ:ropes Cover Ñβ Ñβ)(M:ropes Cover Ñβ Ñα)(W:Canvas G): Canvas G:= fun i=> sluice (∑ j∈Finset.range (3+3*i), spurs P C Ñ Γ M W j i)

def perζ (C:KernelChoices)(Ñ:ChartRatio G) := Fintype.card Axis • logOf (ζ Ñ C.penalty)

def tinge (Z:ropes Cover Ñα Ñα)(Γ:ropes Cover Ñβ Ñβ)(M:ropes Cover Ñβ Ñα)(W:Canvas G): Canvas G:= flatPal Z-snow P C Ñ Γ M W + uband (perζ C Ñ)
lemma plug_site (n:Side): plugζ (stepAt P C n) Ñ= Fintype.card (Site n) • perζ C Ñ:=by unfold plugζ perζ; rw [← mul_smul]; congr 1; exact Fintype.card_prod ..

variable {P C Ñ}
local notation "Sf"=> fun n=>stepAt P C n
local notation "ℐ"=> fun n=> weaveFine (ratioN P.L n) G
local notation "τ"=> fun n=> weaveH (ratioN P.L n) G
variable (C) (P) (Ñ)

section
variable (W:Crude G) {P}
local notation "Ft◇" => fun n:Side=>W (n*P.L)
local notation "Ω" => fun n:Side=>Equiv.refl (Woods G n)
lemma stellar_pack (T:(n:Side)→ Matrix (Woods G (n*P.L)) (Woods G n) ℝ)(n i):
    let S:=(Sf) n; let I:=(ℐ) n; let A:= (τ) n; let K:= allotM I (Ω n) (T n)
    bend A (casePW S Ñ (T n) (Ft◇ n) i)=
        fade (upper 1 K) (bend I (sprig (unhaar Ñ) 0 i))-
        fade (stair (upper 1 K) ladder) (scrub (fun i=>bend A (sprig (jointPen G S) 2 i)) i)-
        fade (upper 1 K) (bend I (scrub (Ft◇ n) i)) := by
   intro S I A K
   let g:=ratioN P.L n
   have h : scrub (fun i=> bend A (sprig (jointPen G S) 2 i)) i= bend A (scrub (sprig (jointPen G S) 2) i):=by unfold scrub; split <;> rfl
   have he {U X:Type}(q:U≃X)(b p:Gen ℝ U) : bend q (b-p)=bend q b-bend q p:=rfl
   rw [casePW,Pi.sub_apply, Pi.sub_apply,h, he,he]; rw [bend_fade I A,bend_fade A A,bend_fade I A, show allotM I A _=upper 1 K from cam_chart g _, show allotM A A (groundM G (T n))=stair (upper 1 K) ladder from ground_chart g _ rfl]
end
-- transport seeds and pull paid ranks
variable {P Ñ}
local notation "Ω" => fun n:Side=>Equiv.refl (Woods G n)
lemma score_move (b:P.Branches C G)(i r:ℕ) : Yields (fun n=> scrub (fun i=>bend ( (τ) n) (sprig (jointPen G ((Sf) n)) 2 i)) i r) (scrub (warren P C G) i r):=by
  by_cases h':i=0 <;> simp only [scrub, h', ↓reduceIte]; · exact Yields.zero
  exact spew P C b i r
lemma song_move {i:ℕ} {W:Crude G} {Z:Canvas G} (b:Yields (fun n=> W n i r) (Z i r)): Yields (fun n=> bend ((ℐ) n) (scrub (W (n*P.L)) i) r) (plants P.L (scrub Z i) r):= by
  apply bend_yields (P:=fun v=> scrub (W v) i)
  by_cases h:i=0<;> simp only [scrub,h,↓reduceIte]; · exact Yields.zero
  exact b

set_option maxHeartbeats 600000 in
lemma star_pages {M:ropes Cover (Larvae G P.L) (Hooks G)}{W:Crude G} {Z:Canvas G}{T : (n:Side)→ Matrix (Woods G (n*P.L)) (Woods G n) ℝ}(hT:Pilots (fun n=> allotM (weaveFine (ratioN P.L n) G) (Equiv.refl (Woods G n)) (T n)) M) (h:LocalRatio Ñ) (b:P.Branches C G)(i r:ℕ)(e:Yields (fun n=>W n i r) (Z i r)): Yields (fun n=> bend (weaveH (ratioN P.L n) G) (casePW (stepAt P C n) Ñ (T n) (W (n*P.L)) i) r) (stellar P C Ñ M Z i r):=by
  let U (n:Side): ropes (Site n) (Co P.L (Hooks G)) (Hinge G P.L):= upper 1 (allotM (weaveFine (ratioN P.L n) G) (Equiv.refl _) (T n))
  have hp: Pilots U (upper 1 M):= Pilots.one.deck hT
  have hh := prism_fold (Q:=fun n=> bend (weaveFine (ratioN P.L n) G) (sprig (unhaar Ñ) 0 i)) (P:=plants P.L (bearingJ Ñ i)) hp (bend_yields (bloom_pages h i r))
  have hv := prism_fold (Q:=fun n=>scrub (fun i=>bend (weaveH (ratioN P.L n) G) (sprig (jointPen G (stepAt P C n)) 2 i)) i) (P:=scrub (warren P C G) i) (hp.deck' ladder_fold) (score_move C b i r)
  have hf := prism_fold (Q:=fun n=>bend (weaveFine (ratioN P.L n) G) (scrub (W (n*P.L)) i)) (P:=plants P.L (scrub Z i)) hp (song_move (P:=P) e)
  apply ((hh.sub hv).sub hf).congr
  exact Eventually.of_forall fun n=> (congr_fun (stellar_pack C Ñ W (P:=P) T n i) r).symm

end
end YM.WilsonCoeffUV.Bank
