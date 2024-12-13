
#ifndef PAPILOLIB_EXPORT_H
#define PAPILOLIB_EXPORT_H

#ifdef PAPILOLIB_STATIC_DEFINE
#  define PAPILOLIB_EXPORT
#  define PAPILOLIB_NO_EXPORT
#else
#  ifndef PAPILOLIB_EXPORT
#    ifdef papilolib_EXPORTS
        /* We are building this library */
#      define PAPILOLIB_EXPORT __attribute__((visibility("default")))
#    else
        /* We are using this library */
#      define PAPILOLIB_EXPORT __attribute__((visibility("default")))
#    endif
#  endif

#  ifndef PAPILOLIB_NO_EXPORT
#    define PAPILOLIB_NO_EXPORT __attribute__((visibility("hidden")))
#  endif
#endif

#ifndef PAPILOLIB_DEPRECATED
#  define PAPILOLIB_DEPRECATED __attribute__ ((__deprecated__))
#endif

#ifndef PAPILOLIB_DEPRECATED_EXPORT
#  define PAPILOLIB_DEPRECATED_EXPORT PAPILOLIB_EXPORT PAPILOLIB_DEPRECATED
#endif

#ifndef PAPILOLIB_DEPRECATED_NO_EXPORT
#  define PAPILOLIB_DEPRECATED_NO_EXPORT PAPILOLIB_NO_EXPORT PAPILOLIB_DEPRECATED
#endif

#if 0 /* DEFINE_NO_DEPRECATED */
#  ifndef PAPILOLIB_NO_DEPRECATED
#    define PAPILOLIB_NO_DEPRECATED
#  endif
#endif

#endif /* PAPILOLIB_EXPORT_H */
