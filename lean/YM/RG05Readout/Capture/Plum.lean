import YM.RG05Readout.Capture.Knap
import YM.OPE.Backup.Gather
/-!
# One grouped mesh step of an actual Census

Keep even hooked counterterm through grouping without stoving and rereading
arbitrary matched reps. Can give grouped Estimate even WITHOUT uniform group
copy symmetries: number of groups paid via apron on this same Calendar. Use
d64 Restore machinery with trivial permutation witnesses (can't get Phase estimates
by that vacuity! recovery on actual copies needed later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Pantry
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Ribbon Menu Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open Ribbons.Fibers Ribbons.ManyCopies Ribbons.ManyCopies.Muster
open Address Many MergeProof.Float
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge} {n:Side}{k l N:ℕ} {V W:Type}[DecidableEq V] [Fintype V] [DecidableEq W][Fintype W]
variable {Y:Census (Unit×V)}{Z:Census (Unit×W)} {R:Rep G n} {a b c e t y z:ℝ}
variable {P:Unit×V → Three G n}{F: Config G n→ Poly Y} {S:Finset W}
variable (T:Ribbons.Fibers V W){o : Unit× V→Site n} {w:Unit×V→ℝ}
local notation "T!"=> partialGroup Unit T
local notation "ξ"=> Names Unit V
local notation "η"=> Names Unit W
-- projection, kept exactly in designated census
lemma all_le (v:Type*) [DecidableEq v][Fintype v](R:Census v): R.choices ⊆ (Stock.census v).choices:= fun _ _ => by change _∈ _root_.Finset.univ.powerset; exact mem_powerset.mpr (subset_univ _) -- universe/name
local notation "Θ!"=> all_le _ Y
local notation "Θ₁"=> all_le _ Z
-- kernel identity transport only on retained allocations. exact analytic divisors from salt
abbrev Policy (T:Ribbons.Fibers V W)(Y:Census (Unit×V))(Z:Census (Unit×W)) : Prop:=∀ i: Z.Mode,((partialGroup Unit T).plena (route (all_le _ Z) i)).val∈ Y.choices
variable (ht : Policy T Y Z)
def pilot : Poly Y→ₗ[ℂ] Poly Z where
   toFun v:= Marker.Poly.inject (fun p=> v.part ⟨_,ht p⟩)
   map_add' a b:=by ext i;rfl
   map_smul' a b:=by ext i;rfl
local notation "τ"=> R.p.threshold
local notation "ℓ"=> R.p.supportExponent
local notation "s!"=> Ribbons.Salt.scent R.p.B N (ℓ+1/2) 1 (a) 1 t
local notation "S₁"=> Ribbons.Fibers.Salt.tow w (ℓ+1/2) (a/k) l
local notation "U₁"=> fun j:Unit×W=> ∏ i∈ (T!).contents j,S₁ i
local notation "Ω"=> (o ∘ (T!).twig)
set_option maxHeartbeats 980000 in
lemma breakfast (hp:0 < k)(hq:∀ i:Unit×W,((T!).contents i).card ≤ k)
    (h:Alcove R P F o w t a 1)(hv:R.activities.Valid R.p y z)(hA: Arsenal R)(he:2≤ℓ) (hs:∀ i∈ S,T.Solo i) (hw:∀ i,0<w i)(hy:0≤t)(ha:0<a)(hE:a≤1) (hh:Occupancy o N)(hΩ:Occupancy Ω N) (he':∀ i:Unit×V,coverNumber R.p.B ({Ω ((T!).bunch i),o i}:Support n)≤ l)
    (hp': ((R.p.B+R.p.B+1:ℕ):ℝ)^4*(t+N*siteFactor R.p.B*a) ≤ 1/2)
    (hS:((R.p.B+R.p.B+1:ℕ):ℝ)^4*(s!) ≤ 1/2) (hS':Real.exp (s!) - 1 ≤ 1)
    (hc:∀ U,R.eval U ≠ 0)(hF:Integrable F (prior G n)):
    ∃ Q:Unit×W→ Three G n, MenuBoard (R:=Z) R Q (fun U=>pilot T ht (F U)) Ω U₁ (ℓ-2) 1 ∧
        ∀ i:Unit×W, (i.2∈S → Q i=P ((T!).twig i))∧ (i.2∉ S→ Blade R (Ω i) ((Q i).snd.1) (profile R.activities (Q i).snd.2) 0 (4*(1/(U₁ i)))):=by
    obtain ⟨G',hY,hM⟩:= Alcove.opening (Θ!) h
    obtain ⟨H,K,ψ,ν,hT,hK,hX,hL,hG,hC,hR,hΨ,hF'⟩:=hM.chamber
    let K':= (T!); let D: Ribbons.Fibers.Salt (Unit×W) (Unit×V) K' G n:= ⟨o,fun i=>if T.bunch i.2∈ S then 0 else ν i,H,K⟩
    have hτ:D.Breeze R.p.threshold := ⟨hX,hL⟩
    have hf(i:Unit×V): w i*‖D.pepper i‖ ≤ 1:=by change w i*‖if T.bunch i.2∈S then 0 else ν i‖ ≤ _; split; simp; exact hC i
    have hw'(i):0< S₁ i:= Ribbons.Fibers.Salt.towP w _ _ _ hw (by positivity) i
    have hZ'(j: Unit×W):0<U₁ j:= Finset.prod_pos (fun i _=>hw' i)
    obtain ⟨f',hb⟩:= D.materialize N l a 1 1 k hp (J:=w) hA hτ hv hR hw hh zero_le_one hf R.p.B_pos ha hE he' (by norm_num : (0:ℝ)≤1/2) hT hK hq hc (w:=U₁) (fun _=>rfl) hS hS'
    have hJ:= D.rate w (τ) (ℓ+1/2) 1 a N (R.p.B) l hw hh hf R.p.B_pos ha hE he' k hp hq 1 t zero_le_one hT hK (show 0 ≤ ℓ+1/2 by linarith only [he]); let x':= Real.exp (s!) -1
    obtain ⟨hx,hv'⟩:= (D.vessel τ).carries τ (D.wet _ hτ) S₁ U₁ ℓ (1/2) (s!) (R.p.B) hJ R.p.exponent_pos.le hw' (fun i=>rfl) hS
    let u: Unit→ Motion:= fun _=>(1,false); let m:= Equiv.refl Unit; let F'(i:Unit×V):=(P i).snd.1; let K''(i:Unit×V):=(P i).snd.2
    have hW(i:Unit×W)(he:i∈ crew Unit S): U₁ i ≤ w (K'.twig i):=by
       dsimp only; rw [(crewed _ S hs i he).content,prod_singleton]; unfold Ribbons.Fibers.Salt.tow; have h : 1 ≤ (k:ℝ):=(by exact_mod_cast hp)
       apply le_trans (div_le_self (by apply mul_nonneg (by positivity) (hw _|>.le)) (Real.one_le_exp (by positivity))) (mul_le_of_le_one_left (hw ..|>.le) ((div_le_self ha.le h).trans hE)) -- positivity issue
    let p:= fun _ : Unit=> (0:Site n); let m':=fun _:Unit=>m; let i:Unit:=()
    have h'_ (j:Unit)(he:j≠ ()):False:= he (Subsingleton.elim ..)
    let f(i:Unit×W):= if i.2∈ S then F' (K'.twig i) else D.debt τ i; let g(i:Unit×W):= if i.2∈S then K'' (K'.twig i) else f' i
    obtain ⟨hx',hH,hK',hV⟩:= lodging (C:=ν) (q:=G') (v:=i) (P:=u) (E:=p) (B:=m') (hr:=fun i=> (show D.pepper i= _ from rfl)) hs hτ rfl hF' (fun j he=> (h'_ j he).elim) (fun j he=> (h'_ j he).elim) hb (hx.shrink le_rfl hS' hZ') hv' hR (g:=F') (k:=K'') (fun j he=> (h'_ j he).elim) hG (fun j he=> (h'_ j he).elim) (fun j i U=> hΨ i j U) (fun j U=> (hM.tally ..).trans (congr_fun (hM.price _).symm U)) hM.clef hW ha.le (fun i=> (hZ' i).le) hv
    let Q'(i:Unit×W): Three G n:= (coin R (f i) (g i),f i,g i); let Ξ:= U₁; let Y':=fun U=> Ribbons.Fibers.reap (T!) (G' U)
    have hs0:0 ≤ s!:=by unfold Ribbons.Salt.scent; positivity
    obtain ⟨hy',hy''⟩:= spareStake R.p.B_pos hs0 hy hp' hS
    have hu : Ribbons.ManyCopies.Serves R f (fun i=> profile R.activities (g i)) Y' i u p m' Ω U₁ (ℓ-2) 1:=by
       obtain ⟨Z₁,Z₂,φ,hφ,hS,hV',ht',hL',hr⟩:=hx'.see
       apply Ribbons.ManyCopies.thru (Z:=1) (ζ:=0) (x:=1) (by refine ⟨Z₁,Z₂,φ,hφ,hS,hV'.shrink ?_ le_rfl hZ',ht',hL',hr⟩; linarith only) hv hZ' ha.le hΩ (by linarith only [he]) (hy'.trans_eq (by ring)) hZ' (by simp [Repegs]) zero_le_one (by simp) (by rw [one_mul]; exact hy'') hV hK' hc
    let V':=fun U=> pilot T ht (F U)
    have hV0(U): narrow Θ₁ (Y' U)= V' U:=by
       ext i; rw [narrow_right]; change (G' U).part ( (T!).plena _)=(F U).part ⟨_,ht i⟩; rw [← hY]; exact (narrow_right Θ! (G' U) (⟨_,ht i⟩:Y.Mode)).symm
    have hI: Integrable V' (prior G n):=((pilot T ht).toContinuousLinearMap.restrictScalars ℝ).integrable_comp hF
    refine ⟨Q',⟨hI,fun i=> ⟨hK' i, rfl,?_⟩,?_⟩,fun i=>⟨fun hi=> ?_, fun hi=> ?_⟩⟩
    · have hh (U) : (V' U).part (Z.fire i) = (Q' i).fst U:=by rw [← hV0,narrow_right]; exact hV i U
      have hQ := one_live hI (Z.fire i); simp_rw [hh] at hQ; exact hQ
    · obtain ⟨A0,A1,hV,hV',hv'',hE',hl⟩:=hu -- use name namespace sold?
      have he : Served R f (fun i=>profile R.activities (g i)) Y' Ω Ξ (ℓ-2) 1:= ⟨A0,A1,hV,hV',hv'',hl⟩
      have ht := carry_served (passable Θ₁) (fun _=>1) (q:=Ω) rfl he (w':=Ξ) (fun _=>by rw [norm_one,mul_one]; rfl) hZ' hZ'; change Served _ _ _ V' _ _ _ _; rw [← funext hV0]; unfold narrow; simpa only [one_mul,id_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true] using! ht
    · unfold Q' f g; simp only [hi,if_true]; exact Prod.ext (hM.price _) rfl
    unfold Q' f g; simp only [hi,if_false]; exact (hb.foot i).2
end YM.RG05Readout.Pantry
