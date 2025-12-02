// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{marker::PhantomData, ptr::NonNull};

use crate::{
    SoAVec,
    soable::{SoATuple, SoAble},
};

impl<'a, T: SoAble> IntoIterator for &'a SoAVec<T> {
    type Item = T::Ref<'a>;
    type IntoIter = SoAIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: SoAble> IntoIterator for &'a mut SoAVec<T> {
    type Item = T::Mut<'a>;
    type IntoIter = SoAIterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An iterator over the elements of a `SoAVec`.
///
/// This struct is created by the [`iter`] method on [`SoAVec`].
///
/// [`iter`]: SoAVec::iter
pub struct SoAIter<'a, T: SoAble> {
    ptr: NonNull<u8>,
    capacity: u32,
    index: u32,
    end: u32,
    _marker: PhantomData<&'a T>,
}

impl<'a, T: SoAble> SoAIter<'a, T> {
    pub(crate) fn new(ptr: NonNull<u8>, capacity: u32, end: u32) -> SoAIter<'a, T> {
        SoAIter {
            ptr,
            capacity,
            index: 0,
            end,
            _marker: PhantomData,
        }
    }
}

impl<'a, T: SoAble> Iterator for SoAIter<'a, T> {
    type Item = T::Ref<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.end {
            return None;
        }
        let ptrs = unsafe { T::TupleRepr::get_pointers(self.ptr, self.index, self.capacity) };
        self.index += 1;
        Some(T::as_ref(PhantomData, ptrs))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, T: SoAble> ExactSizeIterator for SoAIter<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        (self.end - self.index) as usize
    }
}

/// A mutable iterator over the elements of a `SoAVec`.
///
/// This struct is created by the [`iter_mut`] method on [`SoAVec`].
///
/// [`iter_mut`]: SoAVec::iter_mut
pub struct SoAIterMut<'a, T: SoAble> {
    ptr: NonNull<u8>,
    capacity: u32,
    index: u32,
    end: u32,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T: SoAble> SoAIterMut<'a, T> {
    pub(crate) fn new(ptr: NonNull<u8>, capacity: u32, end: u32) -> SoAIterMut<'a, T> {
        SoAIterMut {
            ptr,
            capacity,
            index: 0,
            end,
            _marker: PhantomData,
        }
    }
}

impl<'a, T: SoAble> Iterator for SoAIterMut<'a, T> {
    type Item = T::Mut<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.end {
            return None;
        }
        let ptrs = unsafe { T::TupleRepr::get_pointers(self.ptr, self.index, self.capacity) };
        self.index += 1;
        Some(T::as_mut(PhantomData, ptrs))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, T: SoAble> ExactSizeIterator for SoAIterMut<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        (self.end - self.index) as usize
    }
}
