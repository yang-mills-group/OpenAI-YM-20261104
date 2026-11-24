import YM.MSbar.Diagram.Caravan
/-! Combine sewn orientation terms before taking external traces. All momenta conservation on translation
hyperplane, in action-variable notation. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {I:Finset C} {W:Edition C} {m k j n:ℕ} {U:Set ℂ}
  {f g:Functionals C} {L P A:Links C} {d e l : Bit}
namespace Tree
private abbrev scene(C:Type):=((pack C).prod Site.moving).prod Site.moving
def letter (W:Edition C)(d:Bit)(L:Links C)(z:ℂ)(i:ℕ)(a b:Token C i)(v:Mom i):=
    (sign (W.parity b.1) (W.parity a.1+d)/2)*L z i a b v+(sign (W.parity b.1) d/2)*L z i b a (-v)
def root (W:Edition C)(d:Bit)(a b:C)(L:Links C)(f g:Functionals C) : Record (Device (Twins C)):= fun z i x=>
    let u:= x.1.1.1; let v:= channel u;let a:=(a,x.1.2);let b:=(b,x.2)
    letter W d L z i a b (-v) * (f z i ((a,-v)::u)* g z i ((b,v)::x.1.1.2))
private def first (a:C){m:ℕ}(x:Device (Twins C) m):Words C m:= ((a,x.1.2),-channel x.1.1.1)::x.1.1.1
private def second (a:C){m:ℕ}(x:Device (Twins C) m):Words C m:= ((a,x.2),channel x.1.1.1)::x.1.1.2
private lemma access {a:C}: Draw (scene C) (arena C) (fun _ => first a):=by
    constructor
    · intro i j V p; unfold first; change (line C).move V (_::_)=((a,V p.1.2),-channel ((line C).move V p.1.1.1))::_; rw [Domain.work,map_neg,quiet_move]; rfl
    intro E _ _ _ m x hx
    have hp : Domain.Plot _ _ _ (fun v:E=> (x v).1.1.1):=hx.1.1.1; refine ⟨Domain.Plot.cons a _ _ hx.1.2 hp.sum.neg hp, fun v=>?_⟩
    unfold Domain.Balanced comp first; rw [channel_cons, neg_add_cancel]
private lemma leave_ {a:C}: Draw (scene C) (arena C) (fun _=>second a):=by
    constructor
    · intro i j V p; unfold second; change (line C).move V (_::_)= ((a,V p.2),channel ((line C).move V p.1.1.1))::_; rw [Domain.work,quiet_move]; rfl
    intro E _ _ _ m x hx
    have hp : Domain.Plot _ _ _ (fun v:E=> (x v).1.1.1):=hx.1.1.1; exact ⟨Domain.Plot.cons a _ _ hx.2 hp.sum hx.1.1.2.1,fun v=> (channel_cons _ _).trans (hx.1.1.2.2 v)⟩
variable (hf:Full U k W d f) (hg:Full U n W e g) (hL:Pilot U j W l L)
include hf hg hL
private lemma root_cost (a b:C): Eligible U (j+(k+n)) (scene C) (root W d a b L f g):= by
    let p1 (i:ℕ)(x: Device (Twins C) i):Here i := (-channel x.1.1.1,x.1.2,x.2); let p2(i:ℕ)(x: Device (Twins C) i):Here i:= ( - (p1 i x).1,x.2,x.1.2)
    have he : Draw (scene C) home p1:=by
       constructor
       · intro i j V p; change (taxi V (-channel p.1.1.1),_)=(-channel ((line C).move V p.1.1.1),_); rw [map_neg,quiet_move]; rfl
       intro E _ _ _ i x hx; have hE : Domain.Plot _ _ _ (fun v:E=> (x v).1.1.1):= hx.1.1.1
       exact ⟨(moment_plot _).mpr hE.sum.neg,hx.1.2,hx.2⟩
    have ht : Draw (scene C) home p2:=by
       let f(i) (t:Here i): Here i:= (-t.1,t.2.2,t.2.1); have hp:Draw home home f:=by
          constructor; swap
          · intro E _ _ _ m x hx;exact ⟨(moment_plot _).mpr ((moment_plot _).mp hx.1).neg,hx.2.2,hx.2.1⟩
          intro i j V p; change (taxi V (-p.1),_)=(-taxi V p.1,_); rw [map_neg]; rfl
       exact he.follow hp
    unfold root letter
    exact ((((hL.cost a b).arg he).scale (sign (W.parity b) (W.parity a+d)/2)).add (((hL.cost b a).arg ht).scale (sign (W.parity b) d/2))).mul ((hf.licensed.arg (access (a:=a))).mul (hg.licensed.arg (leave_ (a:=b))))
def charge (W:Edition C)(d:Bit)(a b:C)(L:Links C)(f g:Functionals C):Record (Twins C):=fun z=> duplex (pack C).toMotion (W.vector a) (W.vector b) z (root W d a b L f g z)
lemma root_trace (a b:C): Eligible U (j+(k+n)) (pack C) (charge W d a b L f g):= by
    refine duplex_cost _ _ (root_cost hf hg hL a b) ?_ ?_
    · intro z hz m x w; let p:=-channel x.1
      have h1 : Dim.One (W.vector a) (fun u=> letter W d L z m (a,u) (b,w) p):= ((hL.uniformL a b z hz m p w).scale (sign (W.parity b) (W.parity a+d)/2)).add ((hL.uniformR b a z hz m (-p) w).scale (sign (W.parity b) d/2))
      let v:= g z m (((b,w),channel x.1)::x.2); let F(u:Hat m):= f z m (((a,u),p)::x.1); let q:= (fun u:Hat m=> letter W d L z m (a,u) (b,w) p)
      have hp : Dim.One (W.vector a) (fun u=> F u*v):=Eq.mpr (congr_arg (Dim.One _) (funext fun u=> (show F u*v=(v•F) u from mul_comm ..))) ((hf.colors z hz m a p [] x.1).scale v)
      exact h1.product hp
    intro z hz m x w; let p:=-channel x.1; let v:= f z m (((a,w),p)::x.1)
    have h1 : Dim.One (W.vector b) (fun u=> letter W d L z m (a,w) (b,u) p):= ((hL.uniformR a b z hz m p w).scale (sign (W.parity b) (W.parity a+d)/2)).add ((hL.uniformL b a z hz m (-p) w).scale (sign (W.parity b) d/2))
    exact h1.product ((hg.colors z hz m b (channel x.1) [] x.2).scale v)
end Tree
def splice (W:Edition C)(d:Bit)(L:Links C)(f g:Functionals C):Functionals C:= fun t m x=>∑ a∈W.active,∑ b∈W.active, walk W.parity (Tree.charge W d a b L f g) t m x
variable (hf:Full U k W d f)(hg:Full U n W e g)(hL:Pilot U j W l L)
include hf hg hL
omit hf hL in
lemma splice_quiet {s:ℂ}(hs:s∈U): Quiet (splice W d L f g s m):= by
    intro v hv; refine Finset.sum_eq_zero fun a ha=> Finset.sum_eq_zero fun b hb=> ?_; refine split_clear (W.parity ∘ label) (v:=v) (fun x y he=> ?_)
    apply duplex_zero; intros i M p q; unfold Tree.root; simp only
    -- y transfer
    apply mul_eq_zero_of_right; apply mul_eq_zero_of_right; apply hg.quiet _ hs; rw [channel_cons]
    change channel ((line C).move M x)+channel ((line C).move M y)≠0; rw [quiet_move,quiet_move,←map_add,← channel_plus, channel_move he]; simpa only [ne_eq,map_zero] using (taxi_inj M).ne hv
lemma splice_total : Total U (j+(k+n)) (splice W d L f g):= ⟨Eligible.sum' _ (fun i _ => Eligible.sum' _ fun k _=> walk_cost _ (Tree.root_trace hf hg hL i k)),fun _ hz _=>splice_quiet hg hz⟩
end YM.MSbar.Diagram
