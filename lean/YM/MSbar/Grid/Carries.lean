import YM.MSbar.Grid.Calls

/-! Limit receipt on successive pin operators. Uniform compact support is used for each loop at any
fixed (positive IR) scale, not paid as part of a vacuum estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Finsupp Super Finset Filter Set MeasureTheory
open scoped BigOperators Classical Topology
variable {C M:Type*} [AddCommGroup M] [MeasurableSpace M] [TopologicalSpace M] {μ:Measure M} {B:Snap M μ}
  {I:Finset C} {F G: ℕ→ Amps C M}{f g:Amps C M}{k : Bit}{p : C→Bit} {S: Line C M} [IsTopologicalAddGroup M]

-- loop operator with Fourier volume convention folded in μ. Smooth later.
def loop (μ:Measure M)(I:Finset C)(S:Line C M)(f:Amps C M)(v:Field C M):=∫ x,dotted I S f x v ∂μ
lemma Quiet.loop (hf: Quiet f): Quiet (loop μ I S f):= fun v hv=> by unfold Loops.loop; simp_rw [Quiet.dotted hf v hv]; simp

def twig (B:Snap M μ)(I:Finset C)(S:Line C M)(i:ℕ) : Order (Wave C M):= (↑(B.δ i):ℂ) • laps (Stocking I (B.layer i) S)
namespace Copies
variable (hf : Copies B.clan F f)
include hf
section
variable [FirstCountableTopology M] [T2Space M] [BorelSpace M] [IsLocallyFiniteMeasure μ]
lemma travel (hs:Supported S I): Copies B.clan (fun i=> twig B I S i (F i)) (loop μ I S f):= by
   refine ⟨fun i=> ((hf.clear i).lap _).scale _,hf.quiet.loop,?_⟩
   intro w hw u hu; obtain ⟨K,hK,hC⟩:=hs.rises
   let g(n:ℕ)(x:M):=dotted I S (F (w n)) x (u.see n)
   simp_rw [twig,LinearMap.smul_apply, Pi.smul_apply,lap (I:=I)] -- lap under?
   change Tendsto (fun n=> B.charge (w n) (g n)) _ _; refine B.goes hw (g:=fun x=> dotted I S f x u.cap) (K:=K) ?_ ?_ hK
   · intro x k v hk hv ht
     let q : Ticket B.clan (w∘k) := ⟨x,v,ht,hv⟩
     refine tendsto_finsetSum _ (fun i hi=> tendsto_finsetSum _ fun j hj=> ?_)
     let y: Deck C B.clan (w∘k):= (i,q)::(j,q.negative)::(u.recover hk)
     have H n : y.see n=((i,v n)::(j,-v n)::u.see (k n)):= by change _=_::_::_; rw [←Deck.see_recover u hk n]; rfl
     have hh:=hf.pilots _ (hw.comp hk) y (fun n=> by rw [H,lead,hu]); rw [show y.cap=(i,x)::(j,-x)::u.cap from (by rw [← Deck.cap_recover u hk]; rfl)] at hh; simp_rw [H] at hh
     exact (((hs.light i j hi hj).tendsto _|>.comp hv).div_const _).mul hh
   intro n x hx; by_contra ha; exact hx (Finset.sum_eq_zero fun a hA=> Finset.sum_eq_zero fun b hB=> by rw [show S a b x=0 from not_not.mp (fun ht=>ha (hC a hA b hB ht)),zero_div,zero_mul])
end
variable {R:Row C M}
private lemma tracks (he:Kinetic p I k R)(hk:∀ x y,Continuous (R x y)){w:ℕ→ℕ}(hw:Tendsto w atTop atTop)(u v:Deck C B.clan w)
    (hp:∀ n,channel (Deck.see (u++v) n)=0) : Tendsto (fun n=> (rotate he).lift (fun s=> F (w n) (u.see n++s)) (v.see n)) atTop (𝓝 ((rotate he).lift (fun s=> f (u.cap++s)) v.cap)):=by
       induction v generalizing u with
       | nil=>
           have hz(n): Deck.see ([]:Deck C B.clan w) n=[]:=rfl
           simp only [hz,Deck.cap,List.map_nil,Transport.base]; exact tendsto_const_nhds
       | cons a v ih =>
           rcases a with ⟨x,b⟩;let T:=rotate he;let V(n:ℕ):Amps C M:=fun s=> F (w n) (u.see n++s); let P:Amps C M:=fun s=> f (u.cap++s)
           have h (z:C)(n):channel (Deck.see ((u++[(z,b)])++v) n)=0:= by
               specialize hp n; unfold Deck.see at *; simpa only [List.map_append,List.append_assoc,List.map_cons,List.map_nil,List.cons_append,List.nil_append,channel_plus,channel_cons] using hp
           change Tendsto (fun n=> field (x,b.f n) (T.lift (V n)) (Deck.see v n)) atTop (𝓝 (field (x,b.target) (T.lift P) (Deck.cap v)))
           simp_rw [Transport.leg]; simp only [Pi.add_apply, Pi.smul_apply,smul_eq_mul]
           apply Tendsto.add
           · unfold T; simp_rw [row_here]; refine tendsto_finsetSum _ fun i hi=> (((hk x i).tendsto _).comp b.tend).mul ?_
             unfold V P; have hr:= hf.pilots w hw ((u++[(i,b)])++v) (h i); simpa only [Deck.see,Deck.cap,List.map_append,List.append_assoc,List.map_nil,List.map_cons,List.cons_append,List.nil_append] using hr
           -- sign same
           have hh:=ih (u++[(x,b)]) (h x)
           change Tendsto (fun n=> sign k (p x)*T.lift (field (x,b.f n) (V n)) (Deck.see v n)) _ _; unfold V P
           simp only [field,LinearMap.coe_mk,AddHom.coe_mk]
           apply tendsto_const_nhds.mul -- hm
           simpa only [T,Deck.see,Deck.cap,List.map_append,List.append_assoc,List.map_nil,List.map_cons,List.cons_append,List.nil_append] using hh
lemma kinetic (he:Kinetic p I k R)(h:∀ x y,Continuous (R x y)): Copies B.clan (fun n=> (rotate he).lift (F n)) ((rotate he).lift f):=
   ⟨fun n=>(hf.clear n).rotation he,hf.quiet.rotation he,fun w hw u hu=>hf.tracks he h hw ([]:Deck C B.clan w) u hu⟩
end Copies
end YM.MSbar.Loops
