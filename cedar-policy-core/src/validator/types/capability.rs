/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use smol_str::SmolStr;
use std::collections::HashSet;

use crate::ast::{BinaryOp, ExprKind, Expr, Literal, ExprShapeOnly};
use crate::ast::EntityType;


/// A set of capabilities. Used to represent knowledge about attribute existence
/// before and after evaluating an expression.
#[derive(Eq, PartialEq, Debug, Clone, Default)]
pub struct CapabilitySet<'a>(HashSet<Capability<'a>>);

impl<'a> CapabilitySet<'a> {
    /// An empty capability set
    pub fn new() -> Self {
        CapabilitySet(HashSet::new())
    }

    /// A capability set with a single [`Capability`]
    pub fn singleton(e: Capability<'a>) -> Self {
        let mut set = Self::new();
        set.0.insert(e);
        set
    }

    /// Construct the union of `self` and `other`
    pub fn union(&self, other: &Self) -> Self {
        CapabilitySet(self.0.union(&other.0).cloned().collect())
    }

    /// Construct the intersection of `self` and `other`
    pub fn intersect(&self, other: &Self) -> Self {
        CapabilitySet(self.0.intersection(&other.0).cloned().collect())
    }

    /// Does this capability set contain the given [`Capability`]
    pub fn contains(&self, e: &Capability<'_>) -> bool {
        self.0.contains(e)
    }

        /// filtp(α) — rimuove capabilities che coinvolgono l'operatore `in`
    /// Usato da: AddParent, RemoveParent
    pub fn filtp(&self) -> Self {
        CapabilitySet(
            self.0
                .iter()
                .filter(|cap| !Self::expr_contains_in(cap.on_expr.0.as_ref()))
                .cloned()
                .collect()
        )
    }

    /// filta(f, α) — rimuove capabilities sull'attributo f
    /// Usato da: UpdateAttribute, RemoveAttribute
    pub fn filta(&self, f: &str) -> Self {
        let f_expr = Expr::val(SmolStr::new(f));
        CapabilitySet(
            self.0
                .iter()
                .filter(|cap| cap.attribute_or_tag.0.as_ref() != &f_expr)
                .cloned()
                .collect()
        )
    }

    /// filtt(E, α) — rimuove capabilities che referenziano entità di tipo E
    /// Usato da: UpdateEntity, RemoveEntity
    pub fn filtt(&self, entity_type: &EntityType) -> Self {
        CapabilitySet(
            self.0
                .iter()
                .filter(|cap| {
                    !Self::expr_references_entity_type(cap.on_expr.0.as_ref(), entity_type)
                })
                .cloned()
                .collect()
        )
    }

    fn expr_contains_in(expr: &Expr) -> bool {
        match expr.expr_kind() {
            ExprKind::BinaryApp { op: BinaryOp::In, .. } => true,
            ExprKind::And { left, right } => {
                Self::expr_contains_in(left) || Self::expr_contains_in(right)
            }
            ExprKind::Or { left, right } => {
                Self::expr_contains_in(left) || Self::expr_contains_in(right)
            }
            ExprKind::UnaryApp { arg, .. } => Self::expr_contains_in(arg),
            ExprKind::GetAttr { expr, .. } => Self::expr_contains_in(expr),
            ExprKind::HasAttr { expr, .. } => Self::expr_contains_in(expr),
            _ => false,
        }
    }

    fn expr_references_entity_type(expr: &Expr, entity_type: &EntityType) -> bool {
        match expr.expr_kind() {
            ExprKind::Lit(Literal::EntityUID(uid)) => {
                uid.entity_type() == entity_type
            }
            ExprKind::GetAttr { expr, .. } => {
                Self::expr_references_entity_type(expr, entity_type)
            }
            ExprKind::HasAttr { expr, .. } => {
                Self::expr_references_entity_type(expr, entity_type)
            }
            ExprKind::BinaryApp { arg1, arg2, .. } => {
                Self::expr_references_entity_type(arg1, entity_type)
                    || Self::expr_references_entity_type(arg2, entity_type)
            }
            _ => false,
        }
    }
}

/// Represent a single capability, which is an expression and some attribute that is
/// known to exist for that expression.
#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub struct Capability<'a> {
    /// For this expression
    on_expr: ExprShapeOnly<'a, ()>,
    /// This attribute or tag is known to exist on that expression
    ///
    /// This expression represents the attribute or tag name. It should have type string.
    /// Often this is a string constant, but in the case of tags it can be an expression.
    attribute_or_tag: ExprShapeOnly<'a, ()>,
    /// Is `attribute_or_tag` an attribute name or a tag name
    kind: CapabilityKind,
}

#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
enum CapabilityKind {
    /// This capability is for accessing attributes
    Attribute,
    /// This capability is for accessing tags
    Tag,
}

impl<'a> Capability<'a> {
    /// Construct a new [`Capability`] stating that the attribute `attribute` is
    /// known to exist for the expression `on_expr`
    pub fn new_attribute(on_expr: &'a Expr<()>, attribute: SmolStr) -> Self {
        Self {
            on_expr: ExprShapeOnly::new_from_borrowed(on_expr),
            attribute_or_tag: ExprShapeOnly::new_from_owned(Expr::val(attribute)),
            kind: CapabilityKind::Attribute,
        }
    }

    /// Construct a new [`Capability`] stating that the tag `tag` is
    /// known to exist for the expression `on_expr`
    pub fn new_borrowed_tag(on_expr: &'a Expr<()>, tag: &'a Expr<()>) -> Self {
        Self {
            on_expr: ExprShapeOnly::new_from_borrowed(on_expr),
            attribute_or_tag: ExprShapeOnly::new_from_borrowed(tag),
            kind: CapabilityKind::Tag,
        }
    }

    /// Construct a new [`Capability`] stating that the tag `tag` is
    /// known to exist for the expression `on_expr`
    pub fn new_owned_tag(on_expr: &'a Expr<()>, tag: Expr<()>) -> Self {
        Self {
            on_expr: ExprShapeOnly::new_from_borrowed(on_expr),
            attribute_or_tag: ExprShapeOnly::new_from_owned(tag),
            kind: CapabilityKind::Tag,
        }
    }
}
