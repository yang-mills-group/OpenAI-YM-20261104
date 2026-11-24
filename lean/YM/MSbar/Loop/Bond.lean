import YM.MSbar.Grass.Line

/-! Real Fourier sewing (no hat continuation yet). All external momenta sum to delta. Use
actual additive (lifted, for periodic systems modulo real translations) group with chosen charts
when needed in smooth statements. Here algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Super Function Finset
open scoped BigOperators Classical

variable {C M: Type*} [AddCommGroup M]
abbrev Wave (C M : Type*) := C × M
abbrev Field (C M: Type*) := Super.word (Wave C M)
abbrev Amps (C M : Type*) := Super.Series (Wave C M)
abbrev lift (p:C→Bit) : Wave C M → Bit:= fun x=>p x.1

def channel (v : Field C M) := (v.map Prod.snd).sum
@[simp] lemma channel_nil : channel ([]:Field C M)=0:=rfl
@[simp] lemma channel_cons (a:Wave C M) (v): channel (a::v)= a.2+channel v:= by unfold channel; simp
lemma channel_plus (v w : Field C M): channel (v++w)=channel v+channel w:= by simp [channel]
lemma channel_move {x y : Field C M} (h:x.Perm y) : channel x=channel y:= (h.map _).sum_eq
abbrev Quiet (f : Amps C M) := ∀ s:Field C M, channel s≠0 → f s=0

-- pin helpers
variable {p:C→Bit} {I:Finset C} {f g:Amps C M}
lemma lead (a b:C)(m:M)(v:Field C M): channel ((a,m)::(b,-m)::v)=channel v:=by simp
namespace Quiet
lemma add (h:Quiet f)(h':Quiet g): Quiet (f+g):= fun s hv=> by simp [h s hv,h' s hv]
lemma neg (h:Quiet f): Quiet (-f):= fun s hv=> by simp [h s hv]
lemma sub (h:Quiet f)(h':Quiet g): Quiet (f-g):=by rw [sub_eq_add_neg]; exact h.add h'.neg
lemma scale (h:Quiet f)(r:ℂ): Quiet (r • f):=fun s hv=> by simp [h s hv]
lemma zero : Quiet (0:Amps C M):= fun _ _=> rfl
lemma sum {ι:Type*}{g:ι→Amps C M}{P:Finset ι}(h:∀ i∈P,Quiet (g i)): Quiet (∑ i∈P,g i):=by induction P using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero | insert i P he ih=> rw [Finset.sum_insert he]; exact (h _ (Finset.mem_insert_self ..)).add (ih fun i hi=> h _ (Finset.mem_insert_of_mem hi))
end Quiet

abbrev Line (C M:Type*) := C→C→M→ℂ
-- Band support. Need no reflection, but useful.
def Pace (p:C→Bit)(I:Finset C)(d:Bit)(S:Line C M):Prop:=∀ a∈I,∀ b∈I,∀ r,S a b r≠0→p a+p b=d
variable {S:Line C M} {d:Bit}(L:Finset M)
def Stocking (I:Finset C)(L:Finset M) (S:Line C M): Stock (Wave C M):= ∑ t∈L,∑ a∈I,∑ b∈I,Finsupp.single ((a,t),(b,-t)) (S a b t)
lemma Pace.cells (hs:Pace p I d S): Grade (lift p) d (Stocking I L S):= by
   refine Grade.sum fun t ht=> Grade.sum fun a ha=>Grade.sum (fun b hb=> Grade.single (or_iff_not_imp_left.mpr (hs a ha b hb t)))

-- unintegrated loop kernel
def dotted (I:Finset C)(S:Line C M)(f:Amps C M)(r : M)(v : Field C M) := ∑ a∈I,∑ b∈I,(S a b r/2)*f ((a,r)::(b,-r)::v)
lemma lap (S:Line C M) (f:Amps C M) (v:Field C M) : laps (Stocking I L S) f v=∑ t∈L,dotted I S f t v:=by
   unfold Stocking; simp_rw [laps_sum]; simp only [LinearMap.sum_apply,Finset.sum_apply,laps_single,Pi.smul_apply]; rfl
lemma Quiet.dotted (hf:Quiet f) {t}:Quiet (dotted I S f t):= by
   intro s h; exact Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> by rw [hf _ (by rwa [lead]),mul_zero]
lemma Quiet.lap (hf:Quiet f): Quiet (laps (Stocking I L S) f):= fun s hs=> (_root_.YM.MSbar.Loops.lap _ _ _ _).trans (Finset.sum_eq_zero fun i hi=> Quiet.dotted hf s hs)

-- Tree expression. H sym calls use signed permutations later. No quads on joins.
def price (p:C→Bit)(d:Bit)(a b:C)(S:Line C M)(f g: Amps C M)(x y:Field C M) :ℂ:=
    S a b (-channel x)/2*(sign (p b) (p a+d)*f ((a,-channel x)::x)*g ((b,channel x)::y)) +
    S a b (channel x)/2*(sign (p a) d*f ((b,-channel x)::x)*g ((a,channel x)::y))

def tree (p:C→Bit)(I:Finset C)(d:Bit)(S:Line C M)(f g:Amps C M) : Amps C M:= fun s=>∑ a∈I,∑ b∈ I,split (lift p) (price p d a b S f g) s
lemma Quiet.tree (hg:Quiet g): Quiet (tree p I d S f g):= by
    intro s hs; refine Finset.sum_eq_zero fun a _=>Finset.sum_eq_zero fun b _=> split_clear _ (fun u v hu=> ?_)
    have hp(c:C):g ((c,channel u)::v)=0:=by apply hg; rw [channel_cons]; dsimp only; rw [← channel_plus,channel_move hu]; exact hs
    unfold price; rw [hp a,hp b]; ring
end YM.MSbar.Loops
