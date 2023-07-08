cmake_minimum_required(VERSION 3.16)

project(vain)

if(MSVC)
  set_property(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT vain)
endif()

include_directories(${CMAKE_SOURCE_DIR})
FILE(GLOB SRC ${CMAKE_SOURCE_DIR}/*.cpp)

if(NOT WIN32)
  list(REMOVE_ITEM SRC ${CMAKE_SOURCE_DIR}/wingetopt.cpp)
endif()

# Linux guys can't handle static link
if(WIN32)
  set(OPENSSL_USE_STATIC_LIBS ON)
endif()

find_package(Threads REQUIRED)
find_package(OpenSSL REQUIRED)

add_executable("${PROJECT_NAME}" ${SRC})

if(WIN32 AND NOT MSVC)
  set_target_properties("${PROJECT_NAME}" PROPERTIES LINK_FLAGS "-static")
endif()

target_link_libraries("${PROJECT_NAME}" OpenSSL::Crypto Threads::Threads ${CMAKE_REQUIRED_LIBRARIES})