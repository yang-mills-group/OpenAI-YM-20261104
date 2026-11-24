import YM.MSbar.Diagram.SymbolTree
import YM.MSbar.Loop.Rooted
/-! Analytical continuation of kinetic variations (including antifield equation). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {I:Finset C} {W:Edition C} {m k j n:ℕ} {U:Set ℂ}
  {f g : Functionals C} {L P A:Links C} {d e l : Bit}
namespace Arrow
def read (a:C)(L:Links C)(f:Functionals C): Record (fun m=> Twins C m × Hat m) := fun z m p=>
    match p.1.1 with
    | [v] => L z m v.1 (a,p.2) v.2 * f z m (((a,p.2),v.2)::p.1.2)
    | _ => 0
variable (hf:Full U k W d f) (hP:Pilot U j W l L)
include hf hP
lemma cost (a:C): Eligible U (j+k) ((pack C).prod Site.moving) (read a L f):=by
    refine ⟨fun z hz ⦃m n⦄ V x=> ?_,?_⟩ -- conflict L
    · rcases x with ⟨⟨_|⟨p,_|⟨b,w⟩⟩,v⟩,r⟩ <;> try rfl
      let q:= transient C |>.move V p.1
      have he := hf.total.translates (V:=V) hz (((a,r),p.2)::v); change f z _ ( _::_) = _ at he
      have hp := (hP.cost p.1.1 a).natural _ hz V (p.2,(p.1.2,r))
      exact congr_arg₂ (·*·) hp he
    intro E i1 i2 i3 m x hx
    let p(y:E):= (x y).2; let u y:= (x y).1.1; let v y:= (x y).1.2
    obtain ⟨W,hw⟩:= Gem.derives (show Domain.Plot _ _ _ u from hx.1.1)
    let K:=lines L; have hV : Domain.Plot E C m v:= hx.1.2.1
    have H : Bet U (j+k) (fun z:ℂ×E=> read a L f z.1 m ((List.map (Gem.pay z.2) W,v z.2),p z.2)):= by
       rcases W with _|⟨y,_|⟨b,k⟩⟩ <;> try exact Bet.zero
       have ht : HasTemperateGrowth p:= hx.2
       have hh := hP.applies y.a a (fun q:E=>(y.g q,(y.f q,p q))) (tame_pair y.G (tame_pair y.F ht))
       have he : (arena C).plot (fun q=> ((a,p q),y.g q)::v q):=by
          refine ⟨Domain.Plot.cons a _ _ ht y.G hV,fun r=> ?_⟩
          have hk : channel (u r)+channel (v r)=0:= hx.1.2.2 r; rw [hw] at hk; simpa [Domain.Balanced, Gem.pay] using hk
       exact hh.mul (hf.licensed.ev _ _ he)
    change Bet _ _ (fun z:ℂ×E=> read a L f z.1 m ((u z.2,v z.2),p z.2)); rw [hw]; exact H
-- continue from this

def look (W:Edition C)(L:Links C)(f:Functionals C): Record (Twins C) := fun z m x => ∑ a∈ W.active, metric (pack C).toMotion (W.vector a) z (read a L f z) m x
def tick (W:Edition C)(L:Links C)(f:Functionals C): Functionals C:= walk W.parity (look W L f)
omit hP in
lemma blank (u v:Words C m){z:ℂ}(hz:z∈U)(hp:channel u+channel v≠0):look W L f z m (u,v)=0 := by
    refine Finset.sum_eq_zero fun a ha=> ?_; have he (i:ℕ)(u v:Words C i)(p:channel u+channel v≠0)(x): read a L f z i ((u,v),x)=0:=by
       rcases u with _|⟨b,_|⟨c,w⟩⟩ <;> try rfl
       exact mul_eq_zero_of_right _ (hf.quiet z hz i _ (by simpa using p))
    refine stage_vanish (p:=W.vector a) (read a L f z) z _ _ (fun x=> he m u v hp x) ?_
    intro y; refine he (m+1) ((line C).move _ u) ((line C).move _ v) ?_ y; rw [quiet_move,quiet_move,← map_add]; simpa only [ne_eq,map_zero] using (taxi_inj (up m)).ne hp
lemma total : Total U (j+k) (tick W L f) :=by
    have he(a:C)(z:ℂ)(hz:z∈U) (i:ℕ)(w:Twins C i): Dim.Two (W.vector a) (fun p=> read a L f z i (w,p)):=by
       rcases w with ⟨_|⟨b,_|⟨c,w⟩⟩,v⟩ <;> try exact Dim.Two.zero
       rcases b with ⟨⟨d,f⟩,b⟩; exact (hP.uniformR d a z hz _ b f).product (hf.colors z hz _ a b [] v)
    refine ⟨walk_cost W.parity (Eligible.sum' W.active fun a _=> (cost hf hP a).trace _ (he a)),fun z hz i v hv=> split_clear _ (fun x y h=> blank hf x y hz ?_)⟩
    rw [← channel_plus,channel_move h]; exact hv
lemma transport {z:ℂ} (hz:z∈U) : Kinetic (W.binary m) (W.members m) l (L z m):=by
    intro x y _ k h; have he : W.binary m x+W.binary m y=l:=by apply not_not.mp;intro h';exact h (hP.parity x.1 y.1 h' z hz m (k,x.2,y.2))
    rw [← he,cycle]
lemma lifts {m:ℕ}(hz:(m:ℂ)∈U) : tick W L f m m= (Loops.rotate (transport hf hP hz)).lift (f m m) := by
    rw [rooted (hf:=hf.span _ hz _)]
    change split _ _ = split _ _
    congr! 1; funext x y; unfold flow look -- trace
    rcases x with _|⟨b,_|⟨c,w⟩⟩ <;> simp [Trace.sampling, read,Edition.sum]
omit hf hP in
lemma point (z:ℂ){K:Links C}(hL : L z=K z)(hF:f z=g z): tick W L f z=tick W K g z:=by
    unfold tick walk; have h(a:C) : read a L f z=read a K g z:=by unfold read; rw [hL,hF];
    unfold look; simp_rw [h]
private lemma spans (hz:(m:ℂ)∈U): Homogeneous (lift (W.binary m)) (l+d) (tick W L f m m):=by rw [lifts hf hP hz]; exact (Loops.rotate _).manages (hf.span _ hz _)
lemma polar (hz:(m:ℂ)∈U) : Polar W (tick W L f m m):=by
    refine color (spans hf hP hz) (fun i p v=> ?_); let ψ:= W.vector i; let X:= L (↑m) m; let g:= f (↑m) m; let he:=transport (m:=m) hf hP hz; let H:=Loops.rotate he (M:=Mom m); let r(y:Hat m):Letter C m:=((i,y),p)
    have hi (b:Token C m) : Dim.One ψ (fun y=> X (i,y) b p*g ((b,p)::v)) := by
        simp_rw [mul_comm (X _ _ _)]; exact (hP.uniformL i b.1 m hz m p b.2).scale _
    let R := W.members m; have hp(y) : tick W L f m m (r y::v)=(∑ b∈R,X (i,y) b p*g ((b,p)::v))+ sign l (W.parity i)*H.lift (field (r y) g) v:=by
        rw [lifts hf hP hz]; change field _ (H.lift _) _=_; rw [Transport.leg,Pi.add_apply]; exact congr_arg (· + _) (row_here he v (i,y) p)
    change Dim.One _ (fun y=> tick W L f m m (r y::v)); simp_rw [hp]; refine (one_sum R fun i _=> hi i).add (Dim.One.scale (sign ..) ?_)
    have hx(a): Homogeneous (lift (W.binary m)) (W.parity i+d) (field (r a) g):=(hf.span m hz m).derives (r a)
    change Dim.One _ (fun x=> H.lift (field (r x) g) v); unfold H; simp_rw [rooted he (hx _)]
    apply one_split; intro x y _; rcases x with _|⟨a,_|⟨b,w⟩⟩ <;> unfold flow <;> try exact Dim.One.zero
    refine one_sum R fun j hj=>?_ ; exact (hf.colors m hz m i p [] ((j,a.2)::y)).scale _
lemma full : Full U (j+k) W (l+d) (tick W L f) :=by
   have he : ∀ z:ℂ,z∈U→∀ i,Polar W (tick W L f z i) ∧ Homogeneous (lift (W.binary i)) (l+d) (tick W L f z i):=by
      intro z hz i;rw [point z (L:=L) (K:=fun _=> L z) (g:=fun _=> f z) rfl rfl]; have h:= total (hf.freeze hz) (hP.freeze hz)
      exact ⟨h.choose_color W (fun n=> polar (hf.freeze hz) (hP.freeze hz) (mem_univ (n:ℂ))) z,h.choose_hom W (fun n=> spans (hf.freeze hz) (hP.freeze hz) (mem_univ (n:ℂ))) z⟩
   exact ⟨(total hf hP).safe,(total hf hP).quiet,fun _ hz n=> (he _ hz n).1,fun _ hz n=> (he _ hz n).2⟩
end Arrow
end YM.MSbar.Diagram
