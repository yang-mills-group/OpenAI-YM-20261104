import YM.MSbar.Pole.Sew.Cycle
/-! # Connected compositions with a momentum-carrying tree edge: first
combine all stripping amplitudes. No assumption about disjoint *spacetime* variables here. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Piece
open Set Function Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I]

def extend (u v:Piece I):Piece I:=⟨u.l+v.l,u.g*v.g⟩
def mix (s t:List (Piece I)) := s.flatMap (fun p=> t.map (extend p))
variable {M B C S T:Finset I} {a b:ℤ}
lemma additional (u v:Piece I) (M:Finset I) (a b:ℤ) {r:ℝ}(hr:0<r) :
    roll M ⟨a+b,(extend u v).l⟩ r (extend u v).g= roll M ⟨a,u.l⟩ r u.g * roll M ⟨b,v.l⟩ r v.g:= by
  funext z n x
  unfold roll; let A:Age:=⟨a,u.l⟩; let X:Age:=⟨b,v.l⟩
  have hl : ({a:=a+b,l:=(extend u v).l}:Age).alpha z=A.alpha z+ X.alpha z:= by unfold A X extend; simp [Age.alpha,Age.linear]; ring
  change (r:ℂ)^Age.alpha _ _ * (u.g _ n (move M _ x)*v.g _ n _) = ((r:ℂ)^A.alpha z * _)*((r:ℂ)^X.alpha z *_)
  rw [hl,Complex.cpow_add _ _ (by exact_mod_cast hr.ne'),mul_mul_mul_comm]
lemma aboard (p:Piece I) (s:List (Piece I)) (M:Finset I) (a b:ℤ) {r:ℝ}(hr:0<r): sum (s.map (extend p)) M (a+b) r = roll M ⟨a,p.l⟩ r p.g *sum s M b r:=by
  induction s with
  | nil=>simp
  | cons i s ih=> simp only [List.map_cons,sum_cons,mul_add,additional _ _ _ _ _ hr,ih]
lemma combined {s t:List (Piece I)} (M:Finset I)(a b:ℤ) {r:ℝ}(hr:0<r) : sum (mix s t) M (a+b) r= sum s M a r*sum t M b r:= by
  induction s with
  | nil=>simp [mix]
  | cons i s ih=>
    rw [show mix (i::s) t=t.map (extend i)++mix s t from rfl,sum_cat,sum_cons,add_mul,aboard i t M a b hr,ih]

lemma single {u v:Piece I} (h:Single u M a S B)(p:Single v M b T C)(hb:Disjoint B T)(hc:Disjoint C S) :
    Single (extend u v) M (a+b) (S ∪ T) (B∪C):= by
  obtain ⟨⟨k,hk⟩,hS,hx⟩:=h; obtain ⟨⟨l,hl⟩,hT,hy⟩:=p
  refine ⟨⟨_,hk.mul hl⟩,?_,fun he=>?_⟩
  · unfold Acts at *; exact (hS.and hT).mono fun z hz=> crossing hz.1 hz.2 hb hc
  obtain ⟨h₀,h₁⟩ : u.l=0∧v.l=0:= by change u.l+v.l=0 at he; omega
  unfold rests
  filter_upwards [hx h₀,hy h₁] with z hx hy n x
  obtain ⟨D,hD⟩:=hx n x; obtain ⟨K,hK⟩:=hy n x; refine ⟨_,(hD.mul hK).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r (hr:0<r)
  have hl:= additional u v M a b hr; rw [h₀,h₁,he] at hl; exact (congr_fun (congr_fun (congr_fun hl z) n) x).symm
lemma smash {s t:List (Piece I)} (h:Stack s M a S B)(p:Stack t M b T C)(hb:Disjoint B T)(hc:Disjoint C S) : Stack (mix s t) M (a+b) (S∪ T) (B∪C):= by
  constructor
  · intro z hz; obtain ⟨u,hu,x⟩:=List.mem_flatMap.mp hz; obtain ⟨v,hv,rfl⟩:=List.mem_map.mp x; exact single (h.graded u hu) (p.graded v hv) hb hc
  intro r hr; rw [combined M a b hr]; exact (h.combined r hr).mul (p.combined r hr)
end YM.MSbar.Pole.Piece
