import YM.FVA2.Lambda.Rib
/-!
# Splits, care koszul and link reversal, rejected diagrams by length & zero momentum exactly

 All pointwise -- not integrating named diagrams yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Bead
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open Complex (I)
open Canvas (quad high top_quad line4 triple upperquad trigger)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:ℕ}{t:ℝ}
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))
abbrev summit (D:ℝ→ℝ)(F H:Law G)(l r:List (Lane4 G))(i j:BH G):ℂ:= let p:= -net l ; line4 G D i j p * ( cross (parity j) (degree Ψ l) * F ((i,p)::l) ) * H ((j,-p)::r)
def attach (D:ℝ→ℝ)(F H:Law G)(l r:List (Lane4 G)):ℂ:= ∑ i,∑ j,summit D F H l r i j
variable (R D:ℝ→ℝ)(F H:Law G)(l r w:List (Lane4 G))(i j:BH G)
lemma A_quad : quad G D F H w= scatter Ψ w (Bead.attach D F H):= by
    unfold quad Flux.tree; rw [Pi.smul_apply, show _ • scatter _ w _= scatter Ψ w (( (2:ℂ)⁻¹) • (Flux.attaches parity ( line4 G D ) F H )) from (map_smul ( allocate .. ) _ _).symm ]; apply scatter_congr; intro l r _; rw [ attach ]; simp only [Pi.smul_apply, smul_eq_mul, convertR (K:=line4 G D) (Shells.flipped G D), Finset.mul_sum ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold radius summit; ring
abbrev Prude (F:Law G): Prop:= ∀ w, Course true w→ F w ≠ 0 → degree Ψ w=false
lemma prude_solid (he:Solid true F 0): Prude F:= by
    intro l hl hx; obtain hz:= Classical.byContradiction ( fun (hh:fieldDim ghostNo l≠0) => hx ( he.ghost l hl hh )); obtain hr:= elementary (p:=Ψ) (ghostNo ∘ Prod.fst) l (fun i=> ( Local.BV.split_parity i.1 ).symm); change chargeInt (ghostNo ∘ Prod.fst) l=0 at hz; rw [hr,hz]; rfl
lemma prudeT (G:Gauge): Prude (triple G):= prude_solid _ (Crown G).solid
variable {l r}(hz: net l + net r=0)
lemma since_xor {X Y:Bool}(h:(X ^^ Y)=false): X=Y:= by cases X <;> cases Y <;> simp_all
include hz
lemma summit_swap (hF:Prude F)(hH:Prude H): summit D F H l r i j=cross (degree Ψ l) (degree Ψ r)*summit D H F r l j i:= by
    unfold summit; have hn: -net r=net l:= neg_eq_iff_add_eq_zero.mpr (by rwa [add_comm]); simp only [neg_neg]; rw [ ← hn, neg_neg ]; -- check
    set q:= -(net r)
    -- rewrite reversal
    rw [ show net r= - q from ( by simp [q] ), show line4 G D i j (-q)=_ from ( show Heat.Reverse (line4 G D) parity from Shells.flipped G D ) i j q ]; 
    by_cases h₀:line4 G D j i q=0; swap; -- force match unfolds
    case pos=> rw [h₀]; ring
    case neg=>
        obtain hp:= Shells.closure G D j i q h₀; have hs: parity i=parity j:= since_xor hp -- ^
        by_cases h1:F ((i,-q)::l)=0; · rw [h1]; ring
        by_cases h2:H ((j,q)::r)=0; · rw [h2]; ring
        have hl: parity i= degree Ψ l:= by obtain he:= hF _ (fun _=> by rw [ net_cons, hn ]; simp ) h1; exact since_xor he
        have hr: parity j= degree Ψ r:= by obtain he:= hH _ (fun _=> by rw [net_cons]; exact neg_add_cancel _) h2; exact since_xor he
        rw [← hl,← hr,hs]; cases h:parity j <;> simp <;> ring
lemma opposite (hF:Prude F)(hH:Prude H): Bead.attach D F H l r=cross (degree Ψ l) (degree Ψ r)*Bead.attach D H F r l:= by
    unfold attach; rw [Finset.sum_comm]; simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> summit_swap D F H j i hz hF hH
omit hz
lemma quad_comm (he: net w=0)(hF:Prude F)(hH:Prude H): quad G D F H w= quad G D H F w:= by rw [ A_quad,A_quad,Motif.swap]; apply scatter_congr; intro l r hp; exact ( opposite D H F ( ( split_net hp ).trans he ) hH hF ).symm
lemma a_guard (he:net l=0): Bead.attach D F H l r=0:= by simp [attach,summit, line4,he,Shells.z]
lemma boundedL (hp:l.length≠2): Bead.attach D (triple G) F l r=0:= by
  have hv i: triple G ((i,-net l)::l)=0:= Slice.trank _ (by simp; omega); simp [ attach,summit,hv ]
lemma bound0 : Bead.attach D (triple G) F [] r=0:= boundedL D F ( by simp )
lemma bound1 (i:Lane4 G): Bead.attach D (triple G) F [i] r=0:= boundedL D F ( by simp )
lemma bound3 (i j k:Lane4 G): Bead.attach D (triple G) F (i::j::k::l) r=0:= boundedL D F ( by simp )
-- simp on ≤3 n case with 4 leaves. 
variable (A B Z E: Lane4 G)(hX:A.2+B.2=0)(hY:Z.2+E.2=0)
include hX hY
lemma expand4 : quad G D (triple G) (triple G) [A,B,Z,E] = (2:ℂ)*( cross (Ψ B) (Ψ Z)* Bead.attach D (triple G) (triple G) [A,Z] [B,E] + cross (Ψ A) ((Ψ B) ^^ (Ψ Z))*Bead.attach D (triple G) (triple G) [B,Z] [A,E] ) := by
  have he:= prudeT G
  have h' : ∀ x y:List (Lane4 G), net x+net y=0→Bead.attach D (triple G) (triple G) x y=cross (degree Ψ x) (degree Ψ y)*Bead.attach D (triple G) (triple G) y x:= fun _ _ h=> opposite D _ _ h he he
  rw [A_quad]; -- want simp boundedL with side discharged
  simp only [scatter_cons,scatter_nil, degree_cons,degree_nil, Bool.xor_false,cross_false',one_mul, bound0,bound1,bound3,mul_zero,zero_add,add_zero] -- maybe count
  rw [ a_guard D _ _ (l:=[A,B]) (by simpa [net] using hX),a_guard D _ _ (l:=[Z,E]) (by simpa [net] using hY), h' [B,E] [A,Z] (by rw [ net,net ]; have he:B.2+A.2=0:= (add_comm ..).trans hX; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]; rw [add_add_add_comm,he,add_comm E.2,hY,add_zero] ), h' [A,E] [B,Z] (by unfold net; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]; rw [add_add_add_comm,hX,add_comm E.2,hY, add_zero] ) ]; simp only [degree_cons,degree_nil,Bool.xor_false]; cases Ψ A <;> cases Ψ B <;> cases Ψ Z <;> cases Ψ E <;> simp [cross] <;> ring
end YM.FVA2.Lambda.Bead
