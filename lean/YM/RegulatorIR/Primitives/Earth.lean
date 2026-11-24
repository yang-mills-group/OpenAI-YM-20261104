import YM.RegulatorIR.Budget.Algebra

/-!
Root unfold at positive degrees. Requires free root motions (patch-level
plaquette weight, not fixed sites!) not any quotient-space tensor assumption.
Works also with exponentially extended stamps if absolute quota supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter
open scoped Topology ENNReal BigOperators Classical
variable {X U V Y : Type}{r:ℕ}{P:ℝ}
variable {A: Deck P X Y}

structure Parade (U V: Type) where
 rips : Motion → Equiv.Perm U
 bare : V→U
 rolls : Motion × V ≃ U
 puts : ∀ z,rolls z=rips z.1 (bare z.2)
variable {B : Parade U V}

-- suppress scalar entirely. use positive-degree primitive lobe supplies.
def massive (T: U→Packet X r) : Packet X r:=fun x=>∑' u,T u x
def Rot (A: Deck P X Y)(B:Parade U V)(T:U→Packet X r):Prop:= ∀ d u x,A.dyed (T (B.rips d u)) (A.wind d∘ x)=A.dyed (T u) x
lemma mass_rot {T:U→Packet X r}(H:Rot A B T) : A.Ready (massive T):=by
 intro d z; unfold dyed massive; rw [← tsum_mul_right, ← tsum_mul_right, ← (B.rips d).tsum_eq];apply tsum_congr;intro x; exact H d x z
lemma mass_sym {T:U→Packet X r} (H:∀ i,Packet.IsSym (T i)) : Packet.IsSym (massive T):=by
 intro e x;apply tsum_congr; intro i; exact H i e x

section Places
variable (A B)(q:Tuple Y r)(i: Fin r)

def dances (a : Stalk A.project q) : Motion:= Classical.choose ((A.edges (a.val i) (A.place (q i)) ((congr_fun a.property i).trans (A.placed _).symm)).exists)
lemma danced (a:Stalk A.project q) : A.wind (dances A q i a) (a.val i)=A.place (q i):= by unfold dances; exact Classical.choose_spec ((A.edges (a.val i) (A.place (q i)) ((congr_fun a.property i).trans (A.placed _).symm)).exists)

local notation "Q" => Stalk A.project q
local notation "N" => Nest A q i (A.place (q i))

def tilt (d:Motion)(x:Tuple X r): Tuple X r := A.wind d ∘ x
def gait (z:V × Q) : U × N :={
 fst:= B.rips (dances A q i z.2) (B.bare z.1)
 snd:= ⟨tilt A (dances A q i z.2) z.2.val,funext fun j=>(A.projected ..).trans (congr_fun z.2.property j), danced A q i z.2⟩ }
lemma tilt_j (d:Motion) : Injective (tilt A (r:=r) d):= fun _ _ h=> funext fun j=> (A.wind d).injective (congr_fun h j)
lemma gait_v (d:Motion)(v:V)(z:N) : ∃ x, gait A B q i (v,x)=(B.rolls (d,v),z):=by
 let t: Tuple X r:= tilt A (undo d) z.val; let x: Q:=⟨t,funext fun j=>(A.projected ..).trans (congr_fun z.property.1 j)⟩
 have hx : tilt A d x.val=z.val:=by change A.wind d ∘ (A.wind (undo d) ∘ z.val)=_; rw [A.reversed]; ext1 j; simp
 have hp: dances A q i x=d := (A.edges (x.val i) _ (Eq.trans (congr_fun x.property i) (A.placed (q i)).symm)).unique (danced A q i x) ((congr_fun hx i).trans z.property.2)
 exact ⟨x,Prod.ext (by simpa [gait,B.puts] using congr_arg (fun d=> B.rips d (B.bare v)) hp) (Subtype.ext (by change tilt A _ x.val= _;rw [hp, hx]))⟩

def anthem : V × Q≃ U × N := by
 refine Equiv.ofBijective (gait A B q i) ⟨?_,?_⟩
 · rintro ⟨v,z⟩ ⟨w,t⟩ he; let d:= dances A q i z; let u:= dances A q i t
   have hh:B.rolls (d,v)=B.rolls (u,w):= by rw [B.puts,B.puts];exact congr_arg Prod.fst he
   obtain ⟨hx,hz⟩:= Prod.mk.inj (B.rolls.injective hh); rw [hz]; apply congr_arg;apply Subtype.ext; apply tilt_j A d; have hp : tilt A d z.val=tilt A u t.val:=congr_arg (fun x:U× N=>x.2.val) he;rw [hp,hx]
 rintro ⟨z,a⟩; obtain ⟨⟨d,v⟩,rfl⟩:= B.rolls.surjective z; obtain ⟨x,h⟩:= gait_v A B q i d v a;exact ⟨(v,x),h⟩
end Places

section Uniform
variable [Fintype V]{T: U→Packet X r}
variable (h: Rot A B T)(hh:∀ u,quota (T u) 1 ≠⊤)
include h hh
set_option maxHeartbeats 400000 in
lemma rooting (q:Tuple Y r)(i:Fin r) : A.deckSum (massive T) q = ∑ v, A.scroll (T (B.bare v)) q:=by
 let N:=Nest A q i (A.place (q i)); let Q:= Stalk A.project q; let g (u:U)(z:N):= A.dyed (T u) z.val
 let b (v:V)(z:Q):= A.dyed (T (B.bare v)) z.val; let E:= anthem A B q i
 have hp (x): g (E x).1 (E x).2=b x.1 x.2:= h ..
 have hv : quota (fun p:V×Q=>b p.1 p.2) 1≠⊤:=by
    rw [quota_base,ENNReal.tsum_prod', tsum_fintype]; apply ENNReal.sum_ne_top.mpr
    intro v _; change (∑'z:Q,‖A.dyed _ z.val‖ₑ) ≠⊤; simp_rw [A.dyed_cost]; have hh:=hh (B.bare v); rw [quota_base] at hh; exact ne_top_of_le_ne_top hh (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun p=> ‖T (B.bare v) p‖ₑ))
 have hs: Summable (fun p:V×Q=> b p.1 p.2):= quota_summable (w:=1) (fun _=>le_rfl) hv
 have hG: Summable (fun p:U×N=>g p.1 p.2):= E.summable_iff.mp (by unfold Function.comp; simp_rw [hp];exact hs)
 rw [A.deck_pivot (mass_rot h) q i _ (A.placed _), ← tsum_fintype (L:=SummationFilter.unconditional _)]
 calc
   _ = ∑'z:N,∑'u,g u z:= tsum_congr fun z:N=>by unfold dyed massive; rw [← tsum_mul_right]; rfl
   _ = ∑'u,∑'z:N,g u z:= hG.tsum_comm
   _ = _:= by rw [← hG.tsum_prod, ← E.tsum_eq]; simp_rw [hp]; rw [hs.tsum_prod];rfl
end Uniform
end YM.RegulatorIR.Prim
