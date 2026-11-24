import YM.FVA2.Rank.Dim
import YM.FVA2.Position.Habitat
/-! # D Ward `toll` follows slot parity at all ranks

Prove on actual `MS_Data` via `leader` uniqueness on germs and passage to `Archive`.
No comparing a newly selected cyclization. Build proofs combinable for marks, if desired. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Glazer
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul MS.Heat
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Hem.Mell MS.Dock MS.Train MS.Pearl MS.Halo
open _root_.YM.MS.Shine MS.Color Garment.Wave Garment.Wick Signal Book.Convolve
open Hue MS.Emit
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {J:Type}{m n k:ℕ}{G:Gauge} {r q:ℤ}
variable {X Y F: Flats G}{f:Coat G}{U:Rip G}
local notation "Ω"=> hue G
local notation "V"=> tints G
local notation "Φ"=> sock G
local notation "σ"=> Hue.σ
lemma warp {b:Bool}(A B:Mob G)(hp:closedF U b): Ω (arbor U A B)=arbor U (Ω A) (Ω B):= by
 funext m; change Hue.flip _ ( Plane.Flux.tree _ _ _ _) = Plane.Flux.tree _ _ (Hue.flip _ _ ) (Hue.flip _ _); simp_rw [← black (p:=Landau.parity)]; exact Pilot.Transport.gatherR ( Hue.port (U m) ) (A m) ( B m ) (hp m) (hp m)
lemma spin_bg {b:Bool}(hp:closedF U b)(i j:Coat G): Φ ( tapeB (squad U) i j )=tapeB (squad U) (Φ i) (Φ j):= funext fun z=> warp (i z) (j z) hp
lemma stem {b:Bool}(hp:closedF U b)(X Y:Flats G): V (TreeN U X Y)= TreeN U (V X) (V Y):= by
 induction X using Finsupp.induction_linear with
 | zero=> simp
 | add i j hi hj=> simp only [map_add,LinearMap.add_apply,hi,hj]
 | single a i=>
    induction Y using Finsupp.induction_linear with
    | zero=> simp
    | add l r hl hr=> simp only [map_add,hl,hr]
    | single j y=> rw [Park.zap,tonal,tonal,tonal,Park.zap,spin_bg hp]
lemma germH {b:Bool}(h:Sun b f)(hp:Knot b U): Spotty (Φ ( swamp U f )) ( swamp U (Φ f)) := by
    filter_upwards [sunny h, high0] with i hi hI; rw [coat_x, swamp_spec hp hi hI, swamp_spec hp (Hue.turn hi) hI, map_smul, sOcean hp hi i hI ]; rfl
lemma cycleH {b:Bool}(h: Moony b X)(hp:Knot b U): Pact (V (CycleN U X)) (CycleN U (V X)):= by
 intro i; rw [tones]; cases i with| zero=> rw [CycleN,bland (by omega),bland (by omega),map_zero] | succ i=> unfold CycleN; rw [blade, blade, tones]; exact germH (h i) hp
abbrev cycleP (G:Gauge)(n:ℕ): Flats G→ₗ[ℂ] Flats G:= Hue.σ n • tints G
abbrev sleeve (G:Gauge)(n:ℕ): Coat G→ₗ[ℂ] Coat G:= Hue.σ n • sock G
lemma sh (X: T ( Flats G )) : program G n (fun i=> cycleP G i (X i))= cycleP G n ( program G n X ):= by
    unfold program; rw [ map_smul,map_sum]; congr 1; apply Finset.sum_congr rfl; intro i hi; simp only [ cycleP, LinearMap.smul_apply, map_smul, drive0, stem (cl_a G 0), smul_smul ]; obtain hv := mem_antidiagonal.mp ( Finset.mem_filter.mp hi|>.1 ); rw [ ← hv, Hue.sp,mul_comm ]
lemma bulkH {L H: T (Coat G)}{P:T ( Flats G )}(h:leader G P L H): leader G (fun i=> cycleP G i (P i)) (fun i=> sleeve G i (L i)) (fun i=> sleeve G i (H i)) := by
    intro i; obtain ⟨⟨n,H,hV,hU⟩,h0⟩ := h i; refine ⟨ ⟨ n, Joint.via ( (Direct H).scale (σ i)) ?_, fun j=> ?_,?_ ⟩,fun P'=> by change (cycleP G i) (P i)=0; rw [ h0 P', map_zero ] ⟩
    · rw [sh]; simp only [map_add, cycleP,LinearMap.smul_apply,map_smul, smul_add]; exact common (fun _=> EventuallyEq.rfl) (pact_scaled (cycleH (clockMoon hV) (A_caps G 0)) _)
    · exact ((clash hV) j).smul (s_bk i)
    exact ( Hue.top hU ).smul (s_bk i)
-- real continuum pulse parity
lemma rank2w {U Vv:Mield G m}(h:∀ i,Book.rank 1 ( U i ))(hp:∀ i,Book.rank 1 (Vv i))(i:G.ColorIndex): Book.rank 2 (jaw G m U Vv i) := by
    rw [chew]; exact Rails.sum _ (fun j _=>Rails.sum _ (fun k _=> ((h j).product (hp k)).smul _))
lemma twoQ (i j:Arts.L m)(c:G.ColorIndex): Book.rank 2 ( quill i j c ):= rank2w (fun _=> mon_leaf _ ) (fun _=> mon_leaf _ ) _
lemma twoB (x:Chan G m): Book.rank 2 (blazeV G m x):= by
    rcases x with ⟨_|x,i⟩; · exact Rails.smul _ (rank2w (Vv:=cwave m G) (U:=cwave m G) (fun _=> mon_leaf _) (fun _=> mon_leaf _) i)
    exact rank2w (U:=A m G x) (Vv:=cwave m G) (fun _=> mon_leaf _) (fun _=> mon_leaf _) i
lemma three₀ (G:Gauge): Book.rank 3 ( B₁ G m ):= Rails.add ( F:= top3 G m ) ( Rails.smul _ (Rails.sum _ fun i _=> Rails.sum _ fun j _=> ( Rails.sum _ fun c _=> ( rank_α i j c).product (twoQ _ _ _) ).add (Rails.sum _ fun c _=> (twoQ i j c).product (rank_α _ _ _) ) ) ) ( Rails.sum _ fun i _=> Rails.smul _ ( ( mon_leaf ( onX true i ) ).product (twoB i)) )
lemma four₀ (G:Gauge): Book.rank 4 ( B₂ G m ):= Rails.smul _ (Rails.sum _ fun i _=> Rails.sum _ fun j _=> Rails.sum _ fun c _=> (twoQ i j c).product (twoQ i j c))
lemma pulse_at (G:Gauge)(n:ℕ) :  hue G  (pulseX G n) = σ n • pulseX G n:= by
    rcases n with _|(_|(_|n)); simp only [Up0,map_zero,smul_zero]; rw [pulse1]; funext i; exact (show Hue.flip _ ( B₁ G i )= _ from s2 1 ▸ (ranks _ ( n:=3) (three₀ G))); rw [show pulseX G 2=B₂ G by simp [pulseX,Literal.hiss,χ]]; funext i; exact (show Hue.flip _ ( B₂ G i )= _ from s2 2 ▸ (ranks _ ( n:=4) (four₀ G))); simp [pulseX,Literal.hiss,χ,Finsupp.single_eq_of_ne (show n+1+1+1 ≠ 2 from (by omega))]; rfl
variable {P:T ( Flats G )} {H:T (Coat G)}
theorem spun (h:leader G P (gloss (pulseX G)) H) : ( fun i=> sleeve G i (H i) )= H ∧ ∀ i,Pact (cycleP G i ( P i )) (P i) := by
    obtain he:= bulkH h; rw [show (fun i=> sleeve G i ( gloss (pulseX G) i))=gloss (pulseX G) from ?_] at he
    · exact unique_B he h
    funext i x; change σ i • (Ω (pulseX G i))= _; rw [pulse_at, smul_smul,s_id,one_smul]; rfl
lemma spinning (h:leader G P ( gloss (pulseX G) ) H) (n:ℕ)(y u:ℝ): σ n • (Ω (hereZ 4 (P n) u y))= hereZ 4 ( P n ) u y:= by
    apply Shine.Lift.unique (f:= Parade (P n) 4 y u); swap; exact live0 ( (gang (h n)).dost ); apply Shine.Lift.congr (f:= Parade (cycleP G n (P n)) 4 y u); swap; exact prom ( ( spun h ).2 n ) _ _ _; rw [cycleP, LinearMap.smul_apply, page_smul,funext (card (P n) · 4 y u ) ]; exact Shine.Lift.static ( litS (live0 ( (gang ( h n )).dost ) ) ) _
theorem gone (h:leader G P ( gloss (pulseX G) ) H)(n:ℕ)(c: ℝ×ℝ): Hue.only n ( Archive 4 P n c ):= by
 refine (Hue.only_id ..).mpr ?_; rcases c with ⟨c,t⟩; exact congr_fun ( spinning h n c t ) 0
end YM.FVA2.Position.Glazer
