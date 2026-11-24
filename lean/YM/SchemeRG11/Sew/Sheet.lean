import YM.SchemeRG11.Wolt.Ion
/-! Uniform open slot bounds (before pricing). -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Sew
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt
open scoped Classical
variable {I J:Type*}{m n:ℕ}{G:Gauge}
inductive Page (I:Type*):ℕ→ Paper I ℝ→Prop
| unit:Page I 0 1
| bill {m f}(c:ℝ):Page I m f→ Page I m (c • f)
| past {n f}:Page I n f→Page I (n+1) f
| add{m f g}:Page I m f→Page I m g→Page I m (f+g)
| germ {m f}(v:I): Page I m f→ Page I (m+1) (f*X v)
namespace Page
lemma blank(m:ℕ):Page I m 0:=by induction m with | zero=>convert Page.bill (0:ℝ) (Page.unit (I:=I)) using 1; simp | succ m ih=>apply past ih
lemma cons(c:ℝ) : Page I 0 (C c):=by convert Page.bill c (Page.unit (I:=I)) using 1; rw [smul_eq_C_mul,mul_one]
variable {f g:Paper I ℝ}
lemma neg(h:Page I m f):Page I m (-f):=by simpa using Page.bill (-1) h
lemma sub(h:Page I m f)(p:Page I m g):Page I m (f-g):=by rw [sub_eq_add_neg]; exact .add h p.neg
lemma breathe(h:Page I m f)(q:m≤n):Page I n f:=by induction n,q using Nat.le_induction with| base=>assumption | succ _ _ ih=>apply past ih
lemma crop(f:Paper I ℝ):∃ n,Page I n f:=by induction f using MvPolynomial.induction_on with
 | C c=>exact ⟨0,cons _⟩
 | add a b ha hb=> obtain ⟨m,h⟩:=ha; obtain ⟨n,k⟩:=hb; exact ⟨max m n,.add (h.breathe (le_max_left ..)) (k.breathe (le_max_right ..))⟩
 | mul_X a i h=> exact ⟨_,Page.germ i h.choose_spec⟩
lemma prod(h:Page I m f)(k:Page I n g):Page I (m+n) (f*g):=by
 induction k with
 | unit=>rw [mul_one,Nat.add_zero];exact h
 | @bill n g c k ih=>rw [mul_smul_comm]; exact .bill _ ih
 | past k ih=>exact Page.past ih
 | add h k H K=>rw [mul_add];exact .add H K
 | germ v h ih=>rw [←mul_assoc]; exact .germ v ih
lemma rim (h:Page I m f)(v:I→ℝ):Page I m (vent v f):=by
 induction h with
 | unit=>rw [(vent v).map_one_eq_zero]; apply blank
 | bill c H h=>rw [(vent v).map_smul]; exact Page.bill _ h
 | past p P=>exact .past P
 | add h p H P=>rw [map_add]; exact .add H P
 | @germ m p i h ih=>rw [vent_x,mul_comm (X i)]; exact .add (.bill _ (.past h)) (.germ _ ih)
lemma loom(h:Page I m f)(D:Dose I ℝ):Page I m (D.heat f):=by induction h with
 | unit=> rw [D.heat_one];apply Page.unit
 | bill c h H=> rw [map_smul];exact .bill _ H
 | past p h=>exact .past h
 | add p q h k=>rw [map_add];exact .add h k
 | germ v h k=>rw [D.heat_x,mul_comm (X v)];exact .add (.germ _ k) (.past (k.rim _))
lemma sum(p:J→ Paper I ℝ)(s:Finset J)(h:∀i∈s,Page I m (p i)):Page I m (∑i∈s,p i):=by induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty];exact blank _
 | insert i s hi ih=> rw [Finset.sum_insert hi]; exact .add (h i (by simp)) (ih fun i hi=>h i (by simp [hi]))
lemma renameS(h:Page I m f)(u:I→J):Page J m (MvPolynomial.rename u f):=by induction h with
 | unit=>rw [map_one];exact Page.unit
 | add a b h k=> rw [map_add]; exact .add h k
 | bill c h k=>rw [map_smul];exact .bill _ k
 | past h k=>exact .past k
 | germ v h k=>rw [_root_.map_mul (MvPolynomial.rename _),rename_X]; exact .germ _ k
end Page
lemma health (G:Gauge):∃ n,∀(v:Cover)(i j:Axis),Page _ n (Tree.cost v i j (G:=G)):=by
 choose n H using fun i j=>Page.crop (Tree.cost 0 i j : vellum G)
 let A:Axis × Axis→ ℕ:=fun p=> n p.1 p.2
 obtain ⟨e,h⟩:=Finite.exists_max A; refine ⟨A e,fun v i j=>?_⟩; rw [← honour]; exact ((H i j).breathe (h (i,j))).renameS _
lemma critical (p:pLabel G):∃k,∀ s χ, Page (Shaft G) k (nebula χ s p):=by
 obtain ⟨x,H⟩:= health G; obtain ⟨m,U⟩:=Page.crop (stemZero 1 p); obtain ⟨k,h⟩:=Page.crop (castFirst 1 p)
 refine ⟨max k (x+m),fun s χ=>?_⟩
 unfold nebula; apply Page.add ((h.loom _).breathe (le_max_left ..)); have he:Page (Shaft G) x (North.escort χ s):= Page.sum _ _ (fun a _=> Page.bill _ (Page.sum _ _ (fun i _=>Page.sum _ _ (fun j _=>H ..))))
 rw [castFree]; exact ((he.prod U).sub ((he.prod (U.loom _)).loom _)).breathe (le_max_right ..)
end YM.SchemeRG11.Sew
