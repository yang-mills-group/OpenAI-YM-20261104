import YM.Contacts.Harrier.Font
import YM.Contacts.Harrier.Wand
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Cartons Font Tensor PowerSeries
-- reference vector includes stencil even off-shell. q projection preparatory; no claims about W.
variable {d:ℕ} (H:Labels.Frame G d)
abbrev Address (d:ℕ):= Σ v:Fin (d+1), CardID v.val
abbrev Badge := {q:H.Index×Address d // (H.grades q.1).1+q.2.1.val ≤ d}
variable {H}
namespace Badge
variable (v: Badge H)
abbrev loc := v.1.1
abbrev pocket := v.1.2
abbrev num := v.pocket.1.val
abbrev meter := v.pocket.2
abbrev slot := (H.grades v.loc).2
abbrev pull := (H.grades v.loc).1
abbrev win := v.pull+v.num
lemma win_le : v.win≤ d:= v.2
abbrev phi : Cards := plait v.meter
abbrev read (u:Cards) := pay v.meter u
abbrev key (V:Sketch G)(M i:ℕ):= fill H M (V v.phi) i v.loc
lemma income (w:Badge H) : v.read w.phi= if v.pocket=w.pocket then (1:ℝ) else 0:= by
   rcases v with ⟨⟨a,⟨m,hm⟩,x⟩,hv⟩; rcases w with ⟨⟨b,⟨n,hn⟩,y⟩,he⟩
   change pay x (plait y)= if ((⟨⟨m,hm⟩,x⟩:Address d)=⟨⟨n,hn⟩,y⟩) then 1 else 0
   by_cases h:m=n; · subst n; simp
   rw [pay_close (i:=m) (k:=n) _ _ h, if_neg]; intro ht; exact h (congr_arg (fun x:Address d=> x.1.val) ht); -- fix
   -- ...
end Badge
structure Ink (G:Gauge)(d M:ℕ) where
   prism: Labels.Frame G d
   Hol: Source.Hol G
   strip: Source.SectionData prism
   sound: strip.Sound Hol
   pop: Bid.pop strip
   ready: d≤M
   color:G.ColorIndex
   mask: prism.Index→ bore G
   paint v: Birth.Paints strip (mask v) v M
-- assumption Ink inhabited.Feed later
namespace Ink
variable (A: Ink G d M)
lemma prepare (H:Labels.Frame G d) (V: Source.Hol G) (X:Source.SectionData H) (h:X.Sound V)(hp:Bid.pop X)(u:G.ColorIndex)(hh:d ≤ M): ∃ A: Ink G d M,A.Hol=V ∧ A.prism=H ∧ HEq X A.strip:= by
   choose f G using fun i:H.Index=> Birth.artists X h hp i M ((Planned.PrimaryIntegral295.Film.second_fits H i).trans hh); exact ⟨⟨H,V,X,h,hp,hh,u,f,G⟩,rfl,rfl,HEq.rfl⟩
variable {x:Dye G} (v w:Badge A.prism)
abbrev purse : Sketch G:= fun y=> v.read y • A.mask v.loc
lemma pose : IsLinearMap ℝ (A.purse v) := ⟨fun f g=>by change _ • _=_; unfold Badge.read; rw [map_add,add_smul],fun r g=>by unfold purse Badge.read; rw [map_smul,smul_assoc]⟩
lemma life (hq:d≤ D): Living x M D (A.purse v) ζ:= by
   obtain ⟨p,hp⟩:= (A.paint v.loc).chip x ζ; have H:= A.paint v.loc; let K:= v.loc; let X:= A.mask K; refine ⟨A.pose v, fun z=> (show Based ζ x M X from ⟨H.mount,_,hp⟩).smul (v.read z),?_⟩; intro i j; let hx:= hp.lands i j; obtain ⟨a,ha,h⟩:=pay_cost v.meter; refine ⟨a*p i j,mul_nonneg ha hx.cash,fun z b hb hz=> ((hx.smul _).ist ?_)⟩; exact (mul_le_mul_of_nonneg_right (h z D b (by have hh:=v.win_le; omega) hz) hx.cash).trans_eq (by ring)
lemma character (x:Dye G) (v w:Badge A.prism)(k:ℕ): w.key (A.purse v) M k= if k=0∧v=w then 1 else 0:= by
   let H:= A.paint v.loc; have he: Based 1 x M (A.mask v.loc):=⟨H.mount,H.chip x 1⟩; unfold Badge.key; unfold purse; have hv:=print_basis H ((Planned.PrimaryIntegral295.Film.second_fits ..).trans A.ready) A.pop A.sound A.color w.loc k; rw [show fill _ M (_ • A.mask v.loc) k w.loc= _ from (by simpa only [add_zero,fill_null A.prism x] using fill_linear A.prism he (Based.zero (v:=x) (M:=M) (ζ:=1)) zero_lt_one (v.read w.phi) k w.loc)]; rw [v.income,hv]; have hw:v=w↔v.pocket=w.pocket∧v.loc=w.loc:= ⟨fun h=> ⟨congr_arg Badge.pocket h,congr_arg Badge.loc h⟩,fun ⟨h,h'⟩=> Subtype.ext (Prod.ext h' h)⟩; split_ifs <;> norm_num <;> tauto
-- `priceWord`: solve all projected weights at once, so Clear facts follow even from
-- nonlinear full curvature coordinates of the particular charge. Width preserved.
-- power series open sign as input.Formal linear real prescription
abbrev Matt := Badge A.prism → RodP
def priceWord (V: Sketch G) : A.Matt := fun v=> PowerSeries.mk fun i=> v.key V M i
def draw (W:A.Matt): Sketch G:= ∑ v: Badge A.prism, whip (W v) (A.purse v)
def left (V: Sketch G): Sketch G:= V- A.draw (A.priceWord V)
variable {x:Dye G}{X V:Sketch G}
lemma draw_health (W:A.Matt)(h:d≤D): Living x M D (A.draw W) ζ:= Living.sum _ (fun v _=> (A.life v h).whipM _)
lemma left_health (h:Living x M D V ζ)(ht:d≤D): Living x M D (A.left V) ζ:= h.sub (A.draw_health _ ht)
variable (hp:Living x M D V ζ) (hX: Living x M D X ζ)(ht:0<ζ)
include ht
lemma key_plus (v:Badge A.prism)(i:ℕ)(a:ℝ) (h:Living x M D (V) ζ)(hx:Living x M D (X) ζ): v.key (a • V+X) M i=a*v.key V M i+v.key X M i:= fill_linear _ (h.lineage _) (hx.lineage _) ht ..
lemma price_add (h:Living x M D V ζ)(hx:Living x M D X ζ): A.priceWord (V+X)=A.priceWord V + A.priceWord X:= by funext v; apply PowerSeries.ext; intro n; rw [Pi.add_apply,map_add]; unfold priceWord; simp_rw [PowerSeries.coeff_mk]; simpa only [one_smul,one_mul] using A.key_plus ht v n 1 h hx
omit ht in
lemma price_zero : A.priceWord 0=0:= by ext v i; unfold priceWord; rw [PowerSeries.coeff_mk]; simp only [Badge.key,Pi.zero_apply,fill_null A.prism (x:=((Exterior.coord 0),A.color)),map_zero]
lemma prices_sum {W:ι→Sketch G}(P:Finset ι)(h:∀ v∈ P,Living x M D (W v) ζ): A.priceWord (∑ i∈P,W i)=∑ i∈P,A.priceWord (W i):= by
   induction P using Finset.induction with|empty=> simpa only [Finset.sum_empty] using A.price_zero|insert i u hi ih=> let hX x (ht:x∈u):= h x (mem_insert_of_mem ht); simp only [sum_insert hi,price_add A ht (h i (mem_insert_self ..)) (Living.sum _ hX),ih hX]
-- operations extend over formal local scalar coefficients
include hp
lemma price_scale (s:ℝ):A.priceWord (s • V)=s • A.priceWord V:= by
   funext v; apply PowerSeries.ext; intro n; unfold priceWord; erw [Pi.smul_apply,PowerSeries.coeff_smul,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; simpa only [add_zero,Badge.key,Pi.zero_apply,fill_null A.prism x, smul_eq_mul] using A.key_plus ht v n s hp (Living.zero x M D)
lemma price_shift (n:ℕ): A.priceWord (surge V n)=fun i=> A.priceWord V i * PowerSeries.X^n:= by
   funext v; apply PowerSeries.ext; intro i; unfold priceWord; rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_mk]; exact fill_shift _ (hp.lineage _) ht _ _ _
lemma price_ignite (w:RodP)(v:Badge A.prism) : A.priceWord (whip w V) v=w*(A.priceWord V v):= by
   apply PowerSeries.ext; intro i; rw [PowerSeries.coeff_mul]; unfold priceWord; simp_rw [PowerSeries.coeff_mk]; rw [Badge.key,fill_ignite _ hp ht]; exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b=> pin w a * v.key V M b) i).symm
omit hp ht
lemma solo (v:Badge A.prism): A.priceWord (A.purse v) v=1:= by apply PowerSeries.ext; intro i; unfold priceWord; rw [PowerSeries.coeff_mk,A.character ((Exterior.coord 0),A.color) v,PowerSeries.coeff_one]; simp -- coeff_one orientation
lemma alternate (v w:Badge A.prism)(h:v≠w): A.priceWord (A.purse v) w=0:= by apply PowerSeries.ext; intro i; unfold priceWord; rw [PowerSeries.coeff_mk,A.character ((Exterior.coord 0),A.color),map_zero]; simp [h]
-- Does not claim operator projection unchanged for remaining Wick normalization
lemma pricing (W:A.Matt): A.priceWord (A.draw W)=W:= by
   let x:Dye G:=((Exterior.coord 0),A.color); let f v:=A.life (ζ:=1) (x:=x) v le_rfl; unfold Ink.draw; rw [A.prices_sum zero_lt_one univ (fun i _=> (f i).whipM _)]; funext v; rw [Finset.sum_apply, sum_eq_single_of_mem v (mem_univ _)]; rw [A.price_ignite (f _) zero_lt_one,A.solo,mul_one]; intro t ht hu; rw [A.price_ignite (f _) zero_lt_one,A.alternate t v hu,mul_zero]
include hp ht
lemma left_zero (hq:d≤D): A.priceWord (A.left V)=0:= by unfold left; rw [sub_eq_add_neg,A.price_add ht hp (Living.neg (A.draw_health _ hq)),← neg_one_smul ℝ,A.price_scale (A.draw_health _ (x:=x) (ζ:=ζ) hq) ht,A.pricing,neg_one_smul,add_neg_cancel]
end Ink
end
end YM.Contacts.Harrier
