import YM.X.Sage.Gong
/-!
# Wedge.topo = total ∆ some Ω price to modulus degree5. Exact arithmetic verified.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k m n:ℕ} {V:Type*} {q:ℕ+} {r R:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "U"=> G.ColorIndex
local notation "θ"=> Reed.Horizontal G
local notation "Θ"=> (⊤:Submodule ℝ (Fan G))
local notation "T"=> Tet
local notation "P"=> Curly G
variable (i j l s t:Axis)
local notation "Pt"=> potentialL (G:=G)
local notation "Fθ"=>cubicP (G:=G)
def jumpV (i:Axis)(X:Curly G):= dress (step i) X-X
def jack(i j:Axis)(a:G.ColorIndex): P:= jumpV i (Pt j a)
local notation "J"=> jack (G:=G)
lemma facelift (x:G.ColorIndex)(w:PlaqAxes): faceText w x=jack w.val.1 w.val.2 x-jack w.val.2 w.val.1 x:= by simp only [faceText,Stems.arc,blade,map_add,map_sub,Finsupp.linearCombination_single, one_smul,jack,jumpV,potentialL,dress,rename_X,pointB]; simp [add_zero]; abel
lemma jack_cost (x:G.ColorIndex) : jack i j x∈ verse Θ 2:= by
   rw [show jack i j x=glyph (com (diffA i j x)) from ?_]; exact verse_glyph (k:=1) (grad_row (n:=1) (fun _=>i) ((0,j),x)) (by simp)
   rw [com_text]; unfold jack jumpV potentialL dress diffA; simp only [rename_X,pointB,jetRow,blade,map_sub,Finsupp.linearCombination_single,one_smul,add_zero,zero_add]
lemma life (p w:PlaqAxes): wedge (G:=G) p w = cubicP (J p.val.1 p.val.2) (Pt w.val.1) (Pt w.val.2) - cubicP (J p.val.2 p.val.1) (Pt w.val.1) (Pt w.val.2):= by unfold wedge; simp_rw [facelift,jest,sub_mul, Finset.sum_sub_distrib,cubic_hook]
-- ∗ordered face∗ leading derivative at axis i
def thingD (i j k l:Axis): P:= cubicP (J i j) (Pt k) (Pt l)-cubicP (J i k) (Pt j) (Pt l)+cubicP (J i l) (Pt j) (Pt k)
lemma val_thing : weave G=thingD 0 1 2 3-thingD 1 0 2 3+thingD 2 0 1 3- thingD 3 0 1 2:= by unfold weave; simp only [life,plaq, thingD]; ring
lemma cubic_verse (f g w:U→P)(hf:∀ a:U,f a∈verse Θ d)(hg:∀a,g a∈verse Θ k)(hw:∀a,w a∈verse Θ m)(hr:n ≤ d+(k+m)): cubicP f g w∈ verse Θ n:= by
     apply weaken_v hr; unfold cubicP; apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _; apply Submodule.sum_mem; intro k _; exact Submodule.smul_mem _ _ (verse_mul _ (hf _) (verse_mul _ (hg _) (hw _))) -- heartbeat potential
local notation "D"=> verse Θ
lemma tick_tone : jumpV i (cubicP (Pt j) (Pt s) (Pt l))-thingD (G:=G) i j s l∈ D 5 := by
    unfold jumpV; let Dj:=J i j; let Ds:=J i s; let Dl:=J i l; let U0:=Pt j; let U1:=Pt s; let U2:=Pt l
    change dress (step i) (cubicP U0 U1 U2)-cubicP U0 U1 U2-_∈ _
    have hh (j s l:U→P): dress (step i) (cubicP j s l)=cubicP ((dress (step i)) ∘ j) (dress (step i) ∘ s) (dress (step i) ∘ l):= by simp only [cubicP,map_sum,map_mul,map_smul,Function.comp_apply]
    have he(j:Axis): dress (step i) ∘ Pt j= Pt j+J i j:= funext (fun a=> by change (dress _ _) = Pt _ _+(dress _ _-_); abel)
    rw [hh,show U0= _ from (rfl:U0=Pt j), show U1= _ from(rfl:U1=Pt s), show U2= _ from(rfl:U2=Pt l),he,he,he]
    simp_rw [cubic_left,cubic_mid,cubic_right]; change ((cubicP U0 U1 U2+cubicP U0 U1 Dl)+(cubicP U0 Ds U2+cubicP U0 Ds Dl))+((cubicP Dj U1 U2+cubicP Dj U1 Dl)+(cubicP Dj Ds U2+cubicP Dj Ds Dl)) - _-_∈ _
    let p:=cubicP U0 Ds Dl; let a:=cubicP Dj U1 Dl; let b:=cubicP Dj Ds U2; let c:=cubicP Dj Ds Dl; rw [show _ - thingD (G:=G) i j s l=p+a+b+c from ?_];
    swap; · rw [show thingD i j s l=cubicP (G:=G) Dj U1 U2+cubicP U0 Ds U2+cubicP U0 U1 Dl from ?_]; · unfold U0 U1 U2 p a b c; ring -- let f
            change cubicP Dj U1 U2-cubicP Ds U0 U2+cubicP Dl U0 U1=_; rw [crest U0 Ds U2, ← crest Dl U0 U1, cubic_minus (f:=Ds) (g:=U2)]; ring
    refine (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?p ?a) ?b) ?c)
    case p=> exact cubic_verse _ _ _ (fun _=> verse_x _) (jack_cost _ _) (jack_cost _ _) (by norm_num)
    case a=> exact cubic_verse _ _ _ (jack_cost _ _) (fun _=> verse_x _) (jack_cost _ _) (by norm_num)
    case b=> exact cubic_verse _ _ _ (jack_cost _ _) (jack_cost _ _) (fun _=>verse_x _) (by norm_num)
    case c=> exact cubic_verse _ _ _ (jack_cost _ _) (jack_cost _ _) (jack_cost _ _) (by norm_num)
def ttop (i j k l:Axis):P:= jumpV i (cubicP (Pt j) (Pt k) (Pt l))
def wake (G:Gauge):Curly G:= ttop 0 1 2 3-ttop 1 0 2 3+ttop 2 0 1 3-ttop 3 0 1 2
lemma wakes : wake G-weave G∈ D 5:= by
    rw [val_thing,wake, sub_sub_sub_comm, add_sub_add_comm,sub_sub_sub_comm]; refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_) ?_; all_goals apply tick_tone
lemma tollV : Tot.pillar G-(minus_vertex G + wake G)∈ D 5:= by
     have ht : Tot.pillar G-classic G∈ D 5:= (Stone.sums (G:=G) Finset.univ (d:=4) fun i _=> valve i).2; rw [chorus] at ht; let F:= D 5; have he:= F.sub_mem ht wakes; rw [show Tot.pillar G-(minus_vertex G + weave G)-(wake G-weave G)=Tot.pillar G-(minus_vertex G + wake G) from by ring] at he; exact he
end YM.PositionX.Sage
