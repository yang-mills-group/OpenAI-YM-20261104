import YM.FVA2.Inked.Cloud
import YM.FVA2.Inked.Rotation
import YM.FVA2.Gen.Motto
/-! # Midpoint lattice torch exactly from real scores -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked.Music
open Function Filter Set Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Maxwell Gen Press
open MS MS.Koszul MS.Plane MS.Native MS.Native.Sew MS.Native.Draft MS.Cylinder MS.Cylinder.Taylor MS.Momentum MS.Theater
open MS.Color MS.Arts MS.Motif MS.Landau MS.Landau.Detect MS.Halo MS.Book MS.Heat MS.Tone MS.Plane.Wire Source
open Position.OpenAxis
variable {E F J Y : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge}{H:Hol G}{d:ℕ}(S:XSpace.Survey G H d)
local notation "P"=> E4
local notation "L"=> Lane4 G
local notation "I"=> Complex.I
local notation "W"=> G.Color
local notation "K"=> Cfield G 0
local notation "T"=> tilt S
local notation "ζ"=> Subtype.val (p:=fun x:Edge Cover=> x∈Press.knots S)
variable {A:Play E G}{Z: E→ Sky G} (h:Hall A Z)(F:tilt S→ℝ)(he:germ F)
private abbrev midPos (x:Edge Cover): P:= Work.G03.castPos x.1 +( (1/2:ℝ) • basis x.2 )
lemma midPrice (x:Edge Cover)(l:L): lampX (midPos x) l.2= Integration.mid_charge l.2 x.2 x.1:= by rw [lampX,midPos, Integration.center_point ..,sub_self,mul_zero,add_zero]
private lemma expense (D:Sky G)(x:Edge Cover)(t:ℝ): logQuad D t x=t • D x.2 (t • midPos x) := by unfold midPos logQuad Gen.bill; rw [ smul_add,smul_smul,one_div, ← div_eq_mul_inv ]
private lemma fair (l:L)(j:Press.Local S × Conn G)(t:ℝ): voice l j.1.val.2 (t • midPos j.1.val) j.2 = trim l (knot ζ j) t:=by
   rw [voice_i,trim]; unfold knot; by_cases hj:l.1= at_g (n:=0) j.1.val.2 j.2
   · rw [ if_pos hj, show way (R:=ℝ) id l.1 _=1 from ?_,one_mul ]; · unfold flying lampX; rw [ real_inner_smul_right, show inner ℝ (fixF l.2) _= _ from midPrice j.1.val l ]; rfl
     rw [ hj ]; exact only id _
   rw [ if_neg hj, show way (R:=ℝ) id l.1 _=0 from (by apply need; exact hj),zero_mul] -- underscore
include h
lemma chalk (t:ℝ) (l:L)(hl:l∈A.knows)(i: Local S × Conn G): projector i (campaigning ( Z (A.shots l) ) S t)= t * trim l (knot ζ i) t:= by
    rw [ projector_k, ← fair, campaigning,expense, PiLp.smul_apply, h.aims _ l _ hl ]; rfl
abbrev told (S:XSpace.Survey G H d)(Z:E→ Sky G)(x:E×ℝ): tilt S:= campaigning (Z x.1) S x.2 -- h line? include h?
lemma comfort : ContDiff ℝ ω ( told S Z ):=by
    apply contDiff_pi.mpr; intro i; let X:=i.val; unfold told campaigning; simp_rw [expense]; let m(x:E×ℝ):= (x.1,x.2 • midPos i.val); have hm : ContDiff ℝ ω m:= contDiff_fst.prodMk ( contDiff_snd.smul contDiff_const ); exact contDiff_snd.smul (( h.speaks i.val.2 ).comp hm)
private lemma there (t:ℝ): ∃ v:E→L[ℝ] tilt S, (fun y:E=> told S Z (y,t))=v:= by
   choose v hv using h.story; let X:= ContinuousLinearMap.pi (R:=ℝ) (fun i:Local S=> t • v i.val.2 ( t • midPos i.val ) ); refine ⟨ X, funext fun y=>?_⟩; funext i; unfold told campaigning; rw [expense]; exact congrArg (t • ·) (congr_fun (hv i.val.2 (t • midPos i.val)) y)
omit h
abbrev slate (w:Legs (Lane4 G))(t:ℝ):= shade (fun l j=> (( trim l (knot ζ j) t ):ℂ)) ( region.symm ( ink priv F ) ) w
lemma site (w:Legs (Lane4 G)): Lamp ( slate S F w ) ( fieldVal (Tone.run ( Sew.art ζ F )) (ray w) ):= by
    let f:= ( region.symm ( ink priv F ) ); rw [ show run ( Sew.art ζ F )=shade (fun l j=> paywave l (knot ζ j)) f from study _ paywave f ]; exact focuses _ _ _
private lemma multip {D Q: (Lane4 G)→J→ℂ}{c:ℂ}(w:Legs (Lane4 G)) (H:∀ i∈w,∀ j,D i j=c*Q i j)(f:Cyl J ℂ): shade D f w=c^w.length*shade Q f w:=by
   induction w generalizing f with| nil=> simp|cons i l ih=> obtain ⟨s,hs⟩:=fromCyl f; rw [deriv_lum _ _ f hs,deriv_lum _ _ f hs,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [ H i (List.mem_cons_self ..), ih (fun i hi=> H i ( List.mem_cons_of_mem _ hi )), List.length_cons, pow_succ ]; ring
include h he
lemma scanner (t:ℝ)(w:Legs L)(hw:Active A w) : ink A.shots (fun x:E=> F ( told S Z (x,t) )) w= t^w.length • slate S F w t:= by
    obtain ⟨v,hv⟩:=there S h t; rw [ show (fun x:E=> F ( told S Z (x,t) ))= F∘ v from funext fun x=> congrArg F (congr_fun hv x), ink_ctrl_one _ v he ]; let U:=fun l:L=> v (A.shots l); let P'(l:L)(j: Local S × Conn G):ℝ:= projector j ( U l ); rw [scale_pos priv (v∘ A.shots) P' ?_ he]; · rw [Complex.real_smul,Complex.ofReal_pow ]; apply multip; intro l hl j; unfold P' U; rw [← Complex.ofReal_mul]; exact congrArg ( (↑) : ℝ→ℂ ) (Eq.trans (congrArg (fun y=>projector j y) ( ( congr_fun hv (A.shots l) ).symm ) ) (chalk S h t l (hw l hl) j))
    intro i; exact ( frame ( U i ) ).symm
lemma balcony (i:ℕ)(w:Legs L)(hw:Active A w): torch i (Tone.run (Sew.art ζ F)) w= I^i * MS.Plane.reading (i+w.length) (fun t=> ink A.shots (fun x:E=> F (told S Z (x,t))) w ):= by
    obtain hh:=site S F w; rw [ funext (fun t:ℝ=> scanner S h F he t w hw), factorQ _ _ hh.real ]; exact hh.phase i
end YM.FVA2.Inked.Music
