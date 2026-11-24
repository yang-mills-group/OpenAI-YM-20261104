import YM.FVA2.Gen.EdgeLight
/-! # Family of real smooth connections. Carrying along all nearby links -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision Source Wilson
variable {E F :Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {G:Gauge}{A: Sky G}{J:Labels.Jet G}{H:Hol G}{x:E4}{i:Axis}{k d:ℕ}
local notation "P"=> E4
local notation "U"=> G.mat
local notation "Λ"=> G.lieExp
-- parameter φ(geom)→ paths for all spacings and anchors
abbrev Arc (E: Type)(G:Gauge):= E→ Sky G
local notation "W"=> E × P × ℝ
variable {Z:Arc E G}
def Flo (Z:Arc E G): Prop:= ∀ i:Axis, ContDiff ℝ ∞ (fun x:E×E4=> Z x.1 i x.2)
def drives (Z:Arc E G) (i:Axis)(x: ( E × P × ℝ )×ℝ ):= let a:=x.1; a.2.2 • Z a.1 i ( a.2.1 + (a.2.2*x.2) • basis i )
lemma Flo.this (h:Flo Z)(i:Axis): ContDiff ℝ ∞ (drives Z i):=by
 let f(s:W×ℝ):=s.1.2.2; have hf:ContDiff ℝ ∞ f:= by unfold f; fun_prop
 refine ContDiff.smul hf ( show ContDiff ℝ ∞ (fun x:W×ℝ=> Z x.1.1 i ( x.1.2.1 + (f x*x.2) • basis i )) from ?_ ); apply ( h i ).comp (f:=fun x:W×ℝ=>(x.1.1, x.1.2.1+(f x*x.2) • basis i)); exact (contDiff_fst.comp contDiff_fst).prodMk (((contDiff_fst.comp contDiff_snd).comp contDiff_fst).add ( (hf.mul contDiff_snd).smul contDiff_const ))
lemma Flo.road (h:Flo Z) (x:E): Fluid (Z x):=fun i=> ( h i ).comp (f:=fun y=>(x,y)) (contDiff_const.prodMk contDiff_id)
abbrev Vehicle (E:Type)(G:Gauge):= Axis→ ( E × P × ℝ )→ ℝ→ G.El
def Leads (Q:Vehicle E G) (Z:Arc E G): Prop:= ∀ i:Axis,Meets ( drives Z i ) ( Q i )
lemma Flo.progress (h:Flo Z): ∃ Q:Vehicle E G, Leads Q Z:= by choose Q hQ using fun i:Axis=> meets_real ( h.this i ); exact ⟨Q,hQ⟩
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma meets_into {E'} {S:E×ℝ→ G.Color}{p:E→ℝ→G.El}(h:Meets S p)(f:E'→E): Meets (fun x:E'×ℝ=> S (f x.1,x.2)) (p ∘ f):=fun x=> h (f x)
-- specialize on the Cover for parameter v and spacing y
variable {Q: Vehicle E G}
def earth (Q: Vehicle E G)(x:E): Breeze G:= fun s e=> Q e.2 ( x,s • Work.G03.castPos e.1,s )
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma Leads.air (h:Leads Q Z)(x:E): Air (earth Q x) ( Z x ):= by
    intro i t; have he := h i.2 (x, t • Work.G03.castPos i.1,t); change SolvesLink _ _ at he ⊢; unfold earth; refine ( show SolvesLink ( Q i.2 _ ) _ from ?_ ); convert he using 1; funext s; simp only [slides,drives,spot,smul_add,smul_smul]
lemma Leads.caret (hp:Flo Z)(h:Leads Q Z)(i:Axis) : ContDiff ℝ ∞ (fun x:W=> U ( Q i x 1 )):= ( h i ).smooth ( hp.this i )
lemma Leads.house (hp:Flo Z)(h:Leads Q Z)(i:Axis)(x:E)(v:P): Q i (x,v,0) 1=1:=by apply G.mat_injective; apply Eq.trans (b:=(1:G.Mat)) ?_ G.mat_one.symm; exact (( h i ).equip ( hp.this i ) (x:=(x,v,(0:ℝ))) (fun t=> zero_smul .. ) ).base
lemma Leads.safe (hp:Flo Z)(h:Leads Q Z)(e:Edge Cover): ContDiff ℝ ∞ (fun s:E×ℝ=> U ( bookend (earth Q s.1) s.2 e )):= by let p(s:E×ℝ):W:= (s.1,s.2 • Work.G03.castPos e.1,s.2); exact ( h.caret hp e.2 ).comp (f:=p) ( contDiff_fst.prodMk ( ( contDiff_snd.smul contDiff_const ).prodMk contDiff_snd ) )
-- log on family diagonal in real period
section
variable {Q:Vehicle ℝ G}{Z:Arc ℝ G}
def alongB (Q:Vehicle ℝ G)(i:Axis)(x:E4×ℝ):= G.plog (U (Q i (x.2,x.1,x.2) 1))
lemma Leads.paced (hp:Flo Z)(h:Leads Q Z)(i:Axis)(p:P) : ContDiffAt ℝ ∞ (alongB Q i) (p,0):=by
    let f(x:P×ℝ):= U ( Q i (x.2,x.1,x.2) 1 ); have he: ContDiff ℝ ∞ f:= ( h.caret hp i ).comp (f:=fun x:P×ℝ=> (x.2,x.1,x.2)) (contDiff_snd.prodMk (contDiff_fst.prodMk contDiff_snd)); apply ContDiffAt.comp (f:=f) _ _ he.contDiffAt; unfold f; change ContDiffAt ℝ ∞ G.plog ( U ( Q i ( (0:ℝ),p,(0:ℝ) ) 1 ) ); rw [ h.house hp,G.mat_one ]; exact G.plog_diff.of_le le_top
end
-- extracting paths' Taylor cost jointly on those anchors
lemma priced {p:E×ℝ→ F}(h: ∀ (x:E),ContDiffAt ℝ ∞ p (x,0))(n:ℕ): ContDiff ℝ ∞ (fun s:E=> iteratedDeriv n (fun t:ℝ=> p (s,t)) 0 ) := by
    let L:= ContinuousLinearMap.inr ℝ E ℝ; let D:=(fun s:E=> (s,(0:ℝ))); let X := ContinuousMultilinearMap.apply ℝ (fun _:Fin n=> (E×ℝ)) F (fun i=> L 1); let f:= iteratedFDeriv ℝ n p; rw [ show (fun s:E=>iteratedDeriv n _ _)= X ∘ f ∘ D from ?_ ]; swap
    · funext s; have hx(t:ℝ):D s+t • L 1=(s,t):=Prod.ext (by change s+t • 0=s; simp) (by change 0+t • 1=t; simp); change iteratedDeriv n (fun t:ℝ=> p (s,t)) _=_; rw [ show (fun t:ℝ=>p (s,t))=( fun t:ℝ=> p ( D s+t • L 1 )) from funext fun t=> congrArg p (hx t).symm,line (h s|>.of_le ( WithTop.coe_le_coe.mpr le_top )) ] -- anchor
      rfl
    refine contDiff_iff_contDiffAt.mpr (fun x=> X.contDiff.contDiffAt.comp _ ( (h x |>.iteratedFDeriv_right (m:=∞) ?_ ).comp (f:=D) _ (contDiffAt_id.prodMk contDiffAt_const) ) ); exact_mod_cast WithTop.coe_le_coe.mpr le_top
end YM.FVA2.Gen
