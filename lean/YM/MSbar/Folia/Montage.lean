import YM.MSbar.DeltaM.Town
import YM.MSbar.Pulse.Spot
import YM.MSbar.Lease.Bench
import YM.MSbar.Folia.Marrow
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Film
open Function Filter MeasureTheory Cacao Whisk Kelvin RG Lattice Wilson Tree
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar Analysis Bakery Lattice Precision Push.Uniform
open Next.SectorChange Heath Bulk Heath.Stock Heath.Cottage
variable {G : Gauge} {c f:Side}{S:StepData c f}{p a :ℕ}
    {T W A B t s u α β Z:ℝ}
set_option quotPrecheck false
variable (J:Voice G) (F : Forest S.ratio)
variable (X Y: Support f) (V: Config G c) (U : Config G f)
local notation "I"=> board F X
local notation "A!"=>↥(board F X)
local notation "ρ!"=> fence F (board F X) G -- ambiguous
local notation "Z!"=> Config G f
local notation "W!"=>IV F (board F X) G
local notation "X!"=> SpaceP F X G
variable (m: SpaceP F X G)
local notation "K!"=>draw F X U m t
variable (ν : Positions (Key F G))(γ:ChartRatio G)
local notation "Y!"=> hotel F X Y J V ν A B
variable (R:Rep G f)(i:S.Choices)
local notation "L"=> rental F J R Y i V ν
local notation "z!"=> clipM F X Y Y! γ t m U
variable (g:LocalRatio γ) (C:Matrix (↥(board F X)× G.ColorIndex) (↥(board F X)× G.ColorIndex) ℝ) 
local notation "φ!"=> fLog F X γ t
local notation "Γ"=> Portal.purse z! (fun w:X!=> fLog F X γ t w m U (rental F J R Y i V ν) C)
local notation "ρ"=>fieldLaw C
local notation "q!"=> twirl F (board F X)
-- absolute slice axes


variable {K H δ w j ω' B' κ ι ψ :ℝ}
variable (hV:Clear G J)(v:F.Free→G.Color) (hS :Couch J F ν Y γ v V A B K H W) (hP:X ⊆Y)
local notation "Yθ"=> Y!
local notation "Z0"=> chambers F Y J V ν
local notation "Q"=> imageNear J F
include hV hS hP
local notation "Λ"=> chair F ν v
local notation "D!"=> (imageNear J F ∘ chambers F Y J V ν)
local notation "T!"=> outY J F Y V ν X v U
variable (G':Matrix (Key F G) (Key F G) ℝ) (HP:G'.PosDef) (hU:U∈hotel F X Y J V ν A B)
local notation "α'"=>includeX (G:=G) F X
local notation "v!"=> him J F Y V ν G' X v U
local notation "Aμ"=> v! ∘ (includeX (G:=G) F X)
local notation "Zμ"=>clipM F X Y Y! γ t (v! ∘ α') U
-- w.Center.Collapsed.Program = free Dir measure.P.V.Projections.Hull and inner aperture barycenter
variable {l:Key F G→ Site f}{b cK:ℝ}
variable (Q₀:LoopNet l 0 0 (vanish (includeX (G:=G) F X) G') b) (ht:0<t) (hv:LocalRatio γ)
include HP Q₀ hU ht hv
lemma dial : ‖him J F Y V ν G' X v U-chair F ν v‖ ≤ b*(W+A):=by
    unfold him; simp only [add_sub_cancel_left]; let k:= includeX (G:=G) F X; have ht:= Whisk.LoopNet.hope Q₀
    have hl(i:Key F G): (∑ j, |vanish k G' i j|)≤ b:=by simpa [liftW] using Q₀.glow i
    exact (rows_test hl ht _).trans (mul_le_mul_of_nonneg_left (frozen J F X Y V U ν γ hV v hS hP hU) ht)
variable {d:ℝ}
-- includes sphere.Support shell.No all probability comparison.
lemma enclosed (p:X!)(he: p∈Zμ): ‖t • p‖ ≤ W+B+b*(W+A):=by -- p binder ℕ issue
    let P:= chair F ν v; let i:= v!; have hy:= dial J F X Y V U ν γ hV v hS hP G' HP hU Q₀ ht hv -- binder
    let z:= draw F X U (i∘α') t p; have hp:z∈Y!:= he.1; have hc:= shore J F X Y V ν γ hV v hS hP z hp
    let H:= includeX (G:=G) F X; let u':=imbed H *ᵥ (t • p)
    have hx : u'=(imageNear J F (chambers F Y J V ν z)-P)-(i-P):=by
         rw [show imageNear J F _= _ from sumsY J F X Y V U ν γ hv hV v hS hP G' HP p he]; change u'= i+u'-P-(i-P); abel
    have he : ‖u'‖ ≤ W+B+b*(W+A):=by nth_rw 1 [hx]; exact (norm_sub_le ..).trans (add_le_add hc hy)
    apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans he)).2; intro i; exact le_trans (le_of_eq (congr_arg norm (congr_fun (shares H (secureY F X G) (t•p)) i).symm)) ((norm_le_pi_norm u' (H i)).trans he)
variable (hum : b*(W+A)+d+W ≤ B) (hs0 : b*(W+A)+d ≤ K) -- etc.
local notation "d0"=> b*(W+A)+d
-- Profile term.He.reserve.Word.Y
include hum hs0
lemma includes (p : SpaceP F X G)(hp:‖t • p‖≤ d) : p∈clipM F X Y Y! γ t (him J F Y V ν G' X v U ∘ includeX F X) U:=by
    let P:=chair F ν v; let z:=v!; let H':=includeX (G:=G) F X; let u':=z ∘ H'; let A':=draw F X U u' t p; let a(i):= tape (G:=G) (u'+t •p: X!) i
    have hv':‖z-P‖≤b*(W+A):= dial J F X Y V U ν γ hV v hS hP G' HP hU Q₀ ht hv
    have he : ‖(u'+t •p)-(P∘ H')‖≤ b*(W+A)+d:=by
       have ht:‖u'-P∘H'‖≤ b*(W+A):= (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hv')).2 (fun i=> (norm_le_pi_norm (z-P) (H' i)).trans hv')
       rw [show u'+t•p-P∘H'= (u'-P∘H')+t •p from ?_]; · exact (norm_add_le ..).trans (add_le_add ht hp)
       abel
    have hj(k:↥(board F X)): ‖a k-tint G _ P k.val‖ ≤ shade G *d0:= by
       let w:=(u'+t •p)-(P∘ H'); have hW:‖tint G (↥(board F X)) w k‖≤ shade G*d0:= (norm_le_pi_norm (tint G _ w) k).trans ((tint_le w).trans (mul_le_mul_of_nonneg_left he (shade_pos G).le))
       exact hW
    have hB:B>0:=hS.glued.trans_le hS.lifts; let R₀:= shade G*K; have hR(k:F.Free): ‖v k‖≤ R₀:= hS.sums k
    have hWz(k:↥(board F X)): ‖a k‖≤ H:=by
       have hv:‖ν‖≤ K:=by linarith only [hS.ht,hB]
       let y':=tint G _ ν; have hh:‖y' k.val‖≤ R₀:= (norm_le_pi_norm y' _).trans ((tint_le ν).trans (mul_le_mul_of_nonneg_left hv (shade_pos G).le))
       let j:= tint G _ P k.val; have he : j=y' k.val+v k.val:=by unfold j P chair; rw [map_add, ContinuousLinearEquiv.apply_symm_apply]; rfl
       have hg: ‖j‖≤R₀+R₀:= by rw [he]; exact (norm_add_le ..).trans (add_le_add hh (hR _))
       apply le_trans (b:=R₀+(R₀+R₀)) _ (show _≤H from ?_); · nth_rw 1 [show a k=a k-j+j from (sub_add_cancel ..).symm]; exact (norm_add_le ..).trans (add_le_add ((hj k).trans (mul_le_mul_of_nonneg_left hs0 (shade_pos G).le)) hg)
       have he:=hS.enroll1; have hv:0≤R₀:=(norm_nonneg _).trans hh; linarith only [he,hv]
    have hZ:A'∈Heath.Cottage.basis F J V ν (board F Y\board F X) A :=by
         let v':= PBody F X U (tape (u'+t •p)); exact (safezone F X Y J V ν hV hP v').2 hU.2 -- shadow hp
    refine ⟨⟨?_,hZ⟩, fun i _=>Metric.mem_ball.mpr (show _ < γ.radius from lt_of_le_of_lt (dist_zero_right .. |>.trans_le (hWz i)) hS.enroll3)⟩
    intro i hi
    let k:↥(board F X):=⟨i,hi⟩; have h₁:= tape_it F X U u' t p k
    have hH':0≤R₀ := (norm_nonneg _).trans (hR i); have hδ : R₀ ≤ H:=by linarith only [hH',hS.enroll1]
    have hx: flume F V A' i= G.lieExp (a k)* G.lieExp (- v i):=by
          unfold flume; rw [show canoe F _ i.val=_ from h₁,← hS.emits i, Next.SectorChange.exp_negative]
    let u₁:=fareX F J V A' i; have hv:G.chord (flume F V A' i) ≤ J.δ :=by
         have hp(j:G.Color)(he:‖j‖≤H) : G.chord (G.lieExp j) ≤ J.C*H := ((hV.small j (he.trans hS.enroll2)).2).trans (mul_le_mul_of_nonneg_left he (zero_le_one.trans hV.cost)); rw [hx]; apply (G.chord_triangle ..).trans; exact (add_le_add (hp _ (hWz k)) (hp _ (norm_neg ..|>.trans_le ((hR i).trans hδ)))).trans (by linarith only [hS.enroll4])
    let y':= u₁-a k- - v i; have hk: ‖y'‖≤ W:=by
         unfold y' u₁ fareX; rw [hx]; apply (hV.turns _ _ H hS.enroll2 (hWz k) (norm_neg _|>.trans_le ((hR i).trans hδ))).trans ((mul_le_mul_of_nonneg_left (hWz k) (mul_nonneg (zero_le_one.trans hV.cost) (hH'.trans hδ))).trans _); exact (le_of_eq (by ring: J.C*H*H=J.C*H^2)).trans hS.round
    refine ⟨(hV.near _ hv).2.1,fun j'=> ?_⟩
    change |u₁ j'- _|≤ _; have he': |u' (k,j')+(t•p) (k,j')-P (H' (k,j'))|≤d0:=by exact le_trans (norm_le_pi_norm (u'+t •p - P ∘H') (k,j')) he
    have ht : u' (k,j')+(t•p) (k,j')-P (H' (k,j'))+ y' j'= u₁ j'- ν (i,j'):=by unfold P H' chair y'; simp only [PiLp.neg_apply,PiLp.sub_apply,Pi.add_apply];change u' _ +(t•p) _ - (ν (i,j')+v i j')+(u₁ j'- (u' _+(t•p) _)- - v i j')=_;abel
    rw [← ht]; exact (abs_add_le ..).trans ((add_le_add he' ((PiLp.norm_apply_le ..).trans hk)).trans hum)
end YM.MSbar.Bakery.Film
